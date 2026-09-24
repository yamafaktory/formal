//! A Lean that has already imported Mathlib, kept running between checks.

use std::{
    collections::BTreeMap,
    ffi::OsString,
    io::{
        BufRead,
        BufReader,
        Read,
        Write,
    },
    os::unix::process::CommandExt,
    path::Path,
    process::{
        Child,
        ChildStdin,
        Command,
        Stdio,
    },
    sync::{
        Mutex,
        TryLockError,
        atomic::{
            AtomicBool,
            Ordering,
        },
        mpsc::{
            self,
            Receiver,
            RecvTimeoutError,
        },
    },
    thread,
    time::Duration,
};

use serde::Deserialize;
use serde_json::{
    Value,
    json,
};

use crate::{
    env::Env,
    run::{
        Captured,
        kill_group,
    },
};

/// The only header a proof can have and still be checked warm.
pub const WARM_IMPORT: &str = "import Mathlib";

const DENIED: [&str; 14] = [
    "IO",
    "Lean",
    "#eval",
    "#exit",
    "#guard",
    "run_",
    "elab",
    "macro",
    "syntax",
    "initialize",
    "unsafe",
    "implemented_by",
    "extern",
    "native",
];

const OFF: [&str; 4] = ["off", "none", "0", "false"];

const IMPORT_TIMEOUT: Duration = Duration::from_mins(2);

const MAX_COMMANDS: u32 = 1000;

/// The command to send a warm Lean for `lean_code`, or nothing when it has to be
/// checked cold.
///
/// Import lines are blanked rather than removed, so every position Lean reports
/// is the one it would have reported for the file.
#[must_use]
pub fn warm_command(lean_code: &str) -> Option<String> {
    if DENIED.iter().any(|token| lean_code.contains(token)) {
        return None;
    }
    let mut command = String::with_capacity(lean_code.len());
    let mut in_header = true;
    let mut imported = false;
    for segment in lean_code.split_inclusive('\n') {
        let line = segment.trim_end_matches(['\n', '\r']);
        let trimmed = line.trim();
        if trimmed.starts_with("import") {
            if !in_header || trimmed != WARM_IMPORT {
                return None;
            }
            imported = true;
            command.push_str(&segment[line.len()..]);
            continue;
        }
        if !trimmed.is_empty() {
            in_header = false;
        }
        command.push_str(segment);
    }
    imported.then_some(command)
}

#[derive(Deserialize)]
struct Reply {
    #[serde(default)]
    messages: Vec<Value>,
    env: Option<u64>,
}

/// What `lean --json` would have printed for the same file, from a REPL reply.
///
/// Nothing when the reply is not one the REPL gives for a command it ran.
#[must_use]
pub fn captured_from_reply(reply: &str) -> Option<Captured> {
    let reply: Reply = serde_json::from_str(reply).ok()?;
    reply.env?;
    let mut failed = false;
    let mut lines = Vec::with_capacity(reply.messages.len());
    for mut message in reply.messages {
        let severity = message.get_mut("severity")?;
        match severity.as_str()? {
            "info" => *severity = json!("information"),
            "error" => failed = true,
            _ => {}
        }
        lines.push(message.to_string());
    }
    Some(Captured {
        code: Some(i32::from(failed)),
        stdout: lines.join("\n"),
        stderr: String::new(),
        timed_out: false,
    })
}

/// How to start a warm Lean.
#[derive(Clone, Debug)]
pub struct Launch {
    /// The command, already confined.
    pub argv: Vec<OsString>,
    /// Where it runs.
    pub cwd: std::path::PathBuf,
    /// Its whole environment.
    pub env: BTreeMap<OsString, OsString>,
}

/// What a warm Lean made of a command.
#[derive(Debug)]
pub enum Warmed {
    /// It answered, in the shape a cold run leaves behind.
    Replied(Captured),
    /// It ran past the deadline and was killed.
    TimedOut,
}

enum Asked {
    Answered(String),
    TimedOut,
    Broken,
}

#[derive(Debug)]
struct Session {
    child: Child,
    stdin: ChildStdin,
    replies: Receiver<String>,
    commands: u32,
}

impl Session {
    fn spawn(launch: &Launch) -> std::io::Result<Self> {
        let (program, rest) = launch.argv.split_first().ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::InvalidInput, "nothing to run")
        })?;
        let mut child = Command::new(program)
            .args(rest)
            .current_dir(&launch.cwd)
            .env_clear()
            .envs(&launch.env)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .process_group(0)
            .spawn()?;
        let missing = || std::io::Error::other("a pipe the child was given did not exist");
        let stdin = child.stdin.take().ok_or_else(missing)?;
        let stdout = child.stdout.take().ok_or_else(missing)?;
        Ok(Self {
            child,
            stdin,
            replies: read_replies(stdout),
            commands: 0,
        })
    }

    fn ask(&mut self, command: &Value, timeout: Duration) -> Asked {
        let sent = writeln!(self.stdin, "{command}\n").and_then(|()| self.stdin.flush());
        if sent.is_err() {
            return Asked::Broken;
        }
        match self.replies.recv_timeout(timeout) {
            Ok(reply) => Asked::Answered(reply),
            Err(RecvTimeoutError::Timeout) => Asked::TimedOut,
            Err(RecvTimeoutError::Disconnected) => Asked::Broken,
        }
    }

    fn start(launch: &Launch) -> Result<Self, String> {
        let mut session = Self::spawn(launch).map_err(|e| e.to_string())?;
        match session.ask(&json!({ "cmd": WARM_IMPORT }), IMPORT_TIMEOUT) {
            Asked::Answered(reply) => match captured_from_reply(&reply) {
                Some(captured) if captured.code == Some(0) => Ok(session),
                _ => Err(format!("importing Mathlib failed: {reply}")),
            },
            Asked::TimedOut => Err(format!(
                "importing Mathlib took more than {}s",
                IMPORT_TIMEOUT.as_secs()
            )),
            Asked::Broken => Err("the REPL exited while importing Mathlib".to_string()),
        }
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        kill_group(self.child.id());
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn read_replies(stdout: impl Read + Send + 'static) -> Receiver<String> {
    let (send, receive) = mpsc::channel();
    thread::spawn(move || {
        let mut reply = String::new();
        for line in BufReader::new(stdout).lines() {
            let Ok(line) = line else {
                return;
            };
            if line.trim().is_empty() {
                if !reply.is_empty() && send.send(std::mem::take(&mut reply)).is_err() {
                    return;
                }
                continue;
            }
            reply.push_str(&line);
            reply.push('\n');
        }
    });
    receive
}

/// One warm Lean, shared by every check that finds it free.
#[derive(Debug)]
pub struct Warm {
    session: Mutex<Option<Session>>,
    enabled: AtomicBool,
    max_commands: u32,
}

impl Warm {
    /// A warm Lean that starts on first use, or never when `enabled` is false.
    #[must_use]
    pub fn new(enabled: bool) -> Self {
        Self {
            session: Mutex::new(None),
            enabled: AtomicBool::new(enabled),
            max_commands: MAX_COMMANDS,
        }
    }

    /// Whether checks may still be sent here.
    #[must_use]
    pub fn enabled(&self) -> bool {
        self.enabled.load(Ordering::Relaxed)
    }

    /// Start Lean and import Mathlib now, unless it is already running or busy.
    pub fn warm_up(&self, launch: impl FnOnce() -> Result<Launch, String>) {
        if !self.enabled() {
            return;
        }
        let Some(mut session) = self.free() else {
            return;
        };
        if session.is_none() {
            *session = self.start(launch);
        }
    }

    /// Check `command`, or nothing when it has to be checked cold instead.
    pub fn check(
        &self,
        command: &str,
        timeout: Duration,
        launch: impl FnOnce() -> Result<Launch, String>,
    ) -> Option<Warmed> {
        if !self.enabled() {
            return None;
        }
        let mut guard = self.free()?;
        if guard.is_none() {
            *guard = self.start(launch);
        }
        let session = guard.as_mut()?;
        let asked = session.ask(&json!({ "cmd": command, "env": 0 }), timeout);
        session.commands += 1;
        let recycle = session.commands >= self.max_commands;
        let warmed = match asked {
            Asked::Answered(reply) => captured_from_reply(&reply).map(Warmed::Replied),
            Asked::TimedOut => Some(Warmed::TimedOut),
            Asked::Broken => None,
        };
        if recycle || !matches!(warmed, Some(Warmed::Replied(_))) {
            *guard = None;
        }
        warmed
    }

    fn free(&self) -> Option<std::sync::MutexGuard<'_, Option<Session>>> {
        match self.session.try_lock() {
            Ok(guard) => Some(guard),
            Err(TryLockError::Poisoned(poisoned)) => Some(poisoned.into_inner()),
            Err(TryLockError::WouldBlock) => None,
        }
    }

    fn start(&self, launch: impl FnOnce() -> Result<Launch, String>) -> Option<Session> {
        match launch().and_then(|launch| Session::start(&launch)) {
            Ok(session) => Some(session),
            Err(reason) => {
                self.enabled.store(false, Ordering::Relaxed);
                eprintln!("[LEAN] warm Lean unavailable, checking cold: {reason}");
                None
            }
        }
    }
}

/// Whether `FORMAL_WARM` leaves warm checking on, which it is unless switched off.
#[must_use]
pub fn enabled(env: &Env) -> bool {
    env.get("FORMAL_WARM")
        .is_none_or(|value| !OFF.contains(&value.to_lowercase().as_str()))
}

/// Where `lake build repl` leaves the REPL inside a Lean project.
#[must_use]
pub fn repl_bin(lean_project_dir: &Path) -> std::path::PathBuf {
    lean_project_dir.join(".lake/packages/REPL/.lake/build/bin/repl")
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;

    mod eligibility {
        use super::*;

        #[test]
        fn the_import_is_blanked_and_every_line_keeps_its_number() {
            let command = warm_command("import Mathlib\n\ntheorem t : True := trivial\n")
                .expect("an ordinary proof");
            assert_eq!(command, "\n\ntheorem t : True := trivial\n");
        }

        #[test]
        fn a_crlf_header_keeps_its_line_ending() {
            assert_eq!(
                warm_command("import Mathlib\r\ntheorem t : True := trivial").as_deref(),
                Some("\r\ntheorem t : True := trivial")
            );
        }

        #[test]
        fn a_proof_without_an_import_is_checked_cold() {
            assert_eq!(warm_command("theorem t : True := trivial\n"), None);
        }

        #[test]
        fn any_other_import_is_checked_cold() {
            for code in [
                "import Mathlib.Tactic\ntheorem t : True := trivial",
                "import Mathlib\nimport Mathlib.Tactic\ntheorem t : True := trivial",
                "import Mathlib -- everything\ntheorem t : True := trivial",
            ] {
                assert_eq!(warm_command(code), None, "{code}");
            }
        }

        #[test]
        fn an_import_below_the_header_is_checked_cold() {
            assert_eq!(
                warm_command("import Mathlib\ntheorem t : True := trivial\nimport Mathlib\n"),
                None
            );
        }

        #[test]
        fn anything_that_can_run_code_is_checked_cold() {
            for code in [
                "#eval IO.println \"hi\"",
                "run_cmd pure ()",
                "open Lean Elab in\ntheorem t : True := trivial",
                "elab \"x\" : tactic => pure ()",
                "macro \"x\" : tactic => `(tactic| rfl)",
                "unsafe def f : Nat := 0",
                "theorem t : 2 + 2 = 4 := by native_decide",
                "theorem t : 2 + 2 = 4 := by decide +native",
            ] {
                let code = format!("import Mathlib\n{code}\n");
                assert_eq!(warm_command(&code), None, "{code}");
            }
        }
    }

    #[test]
    fn warm_checking_is_on_unless_switched_off() {
        assert!(enabled(&Env::from_pairs::<&str, &str>([])));
        assert!(enabled(&Env::from_pairs([("FORMAL_WARM", "on")])));
        for value in ["off", "OFF", "0", "false", "none"] {
            assert!(
                !enabled(&Env::from_pairs([("FORMAL_WARM", value)])),
                "{value}"
            );
        }
    }

    mod replies {
        use super::*;

        #[test]
        fn a_clean_reply_is_a_clean_run() {
            let captured = captured_from_reply(r#"{"env": 3}"#).expect("a reply");
            assert_eq!(captured.code, Some(0));
            assert_eq!(captured.stdout, "");
        }

        #[test]
        fn an_error_is_a_failing_exit_and_info_is_spelled_as_lean_spells_it() {
            let captured = captured_from_reply(
                r#"{"messages": [
                    {"severity": "info", "pos": {"line": 7, "column": 51}, "data": "Try this: exact h"},
                    {"severity": "error", "pos": {"line": 3, "column": 38}, "data": "omega could not prove the goal"}
                ], "env": 1}"#,
            )
            .expect("a reply");
            assert_eq!(captured.code, Some(1));
            let lines: Vec<Value> = captured
                .stdout
                .lines()
                .map(|line| serde_json::from_str(line).expect("one message a line"))
                .collect();
            assert_eq!(lines[0]["severity"], "information");
            assert_eq!(lines[1]["pos"]["line"], 3);
        }

        #[test]
        fn a_sorry_warning_does_not_fail_the_exit() {
            let captured = captured_from_reply(
                r#"{"messages": [{"severity": "warning", "data": "declaration uses `sorry`"}], "env": 1}"#,
            )
            .expect("a reply");
            assert_eq!(captured.code, Some(0));
        }

        #[test]
        fn a_repl_error_is_not_a_verdict() {
            assert!(captured_from_reply(r#"{"message": "Unknown environment."}"#).is_none());
            assert!(captured_from_reply("not json").is_none());
        }
    }

    mod sessions {
        use super::*;

        const FAKE_REPL: &str = r#"
            while IFS= read -r line; do
              case "$line" in
                *slow*) sleep 30 ;;
                *crash*) exit 1 ;;
                *broken*) pending='{"message": "Unknown environment."}' ;;
                *fail*) pending='{"messages": [{"severity": "error", "data": "boom"}], "env": 1}' ;;
                '') printf '%s\n\n' "${pending:-{\"env\": 0\}}"; pending= ;;
              esac
            done
        "#;

        fn fake() -> Launch {
            Launch {
                argv: vec!["/bin/sh".into(), "-c".into(), FAKE_REPL.into()],
                cwd: "/".into(),
                env: BTreeMap::from([(OsString::from("PATH"), OsString::from("/usr/bin:/bin"))]),
            }
        }

        fn replied(warmed: Option<Warmed>) -> Captured {
            match warmed {
                Some(Warmed::Replied(captured)) => captured,
                other => panic!("expected a reply, got {other:?}"),
            }
        }

        const SECOND: Duration = Duration::from_secs(1);

        #[test]
        fn a_command_is_answered_and_the_session_is_kept() {
            let warm = Warm::new(true);
            assert_eq!(
                replied(warm.check("ok", SECOND, || Ok(fake()))).code,
                Some(0)
            );
            assert_eq!(
                replied(warm.check("fail", SECOND, || Ok(fake()))).code,
                Some(1)
            );
            let started = warm.check("ok", SECOND, || Err("already running".to_string()));
            assert_eq!(replied(started).code, Some(0));
        }

        #[test]
        fn an_overrun_is_killed_and_the_next_check_starts_afresh() {
            let warm = Warm::new(true);
            let started = Instant::now();
            assert!(matches!(
                warm.check("slow", Duration::from_millis(200), || Ok(fake())),
                Some(Warmed::TimedOut)
            ));
            assert!(started.elapsed() < Duration::from_secs(5));
            assert_eq!(
                replied(warm.check("ok", SECOND, || Ok(fake()))).code,
                Some(0)
            );
        }

        #[test]
        fn a_repl_that_dies_or_misanswers_hands_the_check_back() {
            let warm = Warm::new(true);
            assert!(warm.check("crash", SECOND, || Ok(fake())).is_none());
            assert!(warm.check("broken", SECOND, || Ok(fake())).is_none());
            assert!(warm.enabled());
            assert_eq!(
                replied(warm.check("ok", SECOND, || Ok(fake()))).code,
                Some(0)
            );
        }

        #[test]
        fn a_busy_session_hands_the_check_back_rather_than_queueing() {
            let warm = Warm::new(true);
            let _held = warm.session.lock().expect("an unpoisoned lock");
            assert!(warm.check("ok", SECOND, || Ok(fake())).is_none());
        }

        #[test]
        fn a_session_is_replaced_after_its_quota_of_commands() {
            let mut warm = Warm::new(true);
            warm.max_commands = 2;
            replied(warm.check("ok", SECOND, || Ok(fake())));
            replied(warm.check("ok", SECOND, || Ok(fake())));
            assert!(warm.session.lock().expect("an unpoisoned lock").is_none());
        }

        #[test]
        fn a_launch_that_fails_turns_warm_checking_off() {
            let warm = Warm::new(true);
            assert!(
                warm.check("ok", SECOND, || Err("no REPL".to_string()))
                    .is_none()
            );
            assert!(!warm.enabled());
            assert!(warm.check("ok", SECOND, || Ok(fake())).is_none());
        }

        #[test]
        fn switched_off_it_never_launches() {
            let warm = Warm::new(false);
            assert!(
                warm.check("ok", SECOND, || panic!("nothing to launch"))
                    .is_none()
            );
        }
    }
}
