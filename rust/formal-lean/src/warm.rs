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
        OnceLock,
        TryLockError,
        atomic::{
            AtomicBool,
            Ordering,
        },
        mpsc::{
            self,
            Receiver,
            RecvTimeoutError,
            Sender,
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
    audit,
    env::Env,
    run::{
        Captured,
        kill_group,
    },
    verifier::runs_code,
};

/// The only header a proof can have and still be checked warm.
pub const WARM_IMPORT: &str = "import Mathlib";

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
    if runs_code(lean_code).is_some() {
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
    base: u64,
}

fn spawn_child(launch: &Launch) -> std::io::Result<Child> {
    let (program, rest) = launch
        .argv
        .split_first()
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidInput, "nothing to run"))?;
    Command::new(program)
        .args(rest)
        .current_dir(&launch.cwd)
        .env_clear()
        .envs(&launch.env)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .process_group(0)
        .spawn()
}

type Spawned = std::io::Result<Child>;

#[derive(Debug)]
struct Spawner {
    requests: Sender<(Launch, Sender<Spawned>)>,
}

impl Spawner {
    fn new() -> Self {
        let (requests, received) = mpsc::channel::<(Launch, Sender<Spawned>)>();
        thread::spawn(move || {
            for (launch, answer) in received {
                let _ = answer.send(spawn_child(&launch));
            }
        });
        Self { requests }
    }

    fn spawn(&self, launch: &Launch) -> Spawned {
        let gone = || std::io::Error::other("the thread that starts warm Leans is gone");
        let (answer, answered) = mpsc::channel();
        self.requests
            .send((launch.clone(), answer))
            .map_err(|_| gone())?;
        answered.recv().map_err(|_| gone())?
    }
}

impl Session {
    fn spawn(launch: &Launch, spawner: &Spawner) -> std::io::Result<Self> {
        let mut child = spawner.spawn(launch)?;
        let missing = || std::io::Error::other("a pipe the child was given did not exist");
        let stdin = child.stdin.take().ok_or_else(missing)?;
        let stdout = child.stdout.take().ok_or_else(missing)?;
        Ok(Self {
            child,
            stdin,
            replies: read_replies(stdout),
            commands: 0,
            base: 0,
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

    fn prepare(&mut self, command: &Value, what: &str) -> Result<u64, String> {
        match self.ask(command, IMPORT_TIMEOUT) {
            Asked::Answered(reply) => {
                let env = serde_json::from_str::<Reply>(&reply)
                    .ok()
                    .and_then(|parsed| parsed.env);
                match (captured_from_reply(&reply), env) {
                    (Some(captured), Some(env)) if captured.code == Some(0) => Ok(env),
                    _ => Err(format!("{what} failed: {reply}")),
                }
            }
            Asked::TimedOut => Err(format!(
                "{what} took more than {}s",
                IMPORT_TIMEOUT.as_secs()
            )),
            Asked::Broken => Err(format!("the REPL exited while {what}")),
        }
    }

    fn start(launch: &Launch, spawner: &Spawner) -> Result<Self, String> {
        let mut session = Self::spawn(launch, spawner).map_err(|e| e.to_string())?;
        let imported = session.prepare(&json!({ "cmd": WARM_IMPORT }), "importing Mathlib")?;
        session.base = session.prepare(
            &json!({ "cmd": audit::definition(), "env": imported }),
            "defining the axiom audit",
        )?;
        Ok(session)
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

/// Warm Leans, each taken by whichever check finds it free.
#[derive(Debug)]
pub struct Warm {
    sessions: Vec<Mutex<Option<Session>>>,
    enabled: AtomicBool,
    max_commands: u32,
    spawner: OnceLock<Spawner>,
}

type Slot<'a> = std::sync::MutexGuard<'a, Option<Session>>;

impl Warm {
    /// Up to `processes` warm Leans, each started on first use; none when zero.
    #[must_use]
    pub fn new(processes: usize) -> Self {
        Self {
            sessions: (0..processes).map(|_| Mutex::new(None)).collect(),
            enabled: AtomicBool::new(processes > 0),
            max_commands: MAX_COMMANDS,
            spawner: OnceLock::new(),
        }
    }

    /// Whether checks may still be sent here.
    #[must_use]
    pub fn enabled(&self) -> bool {
        self.enabled.load(Ordering::Relaxed)
    }

    /// How many warm Leans there may be at once.
    #[must_use]
    pub fn processes(&self) -> usize {
        self.sessions.len()
    }

    /// Start every warm Lean now, side by side, rather than on first use.
    pub fn warm_up(&self, launch: impl Fn() -> Result<Launch, String> + Sync) {
        if !self.enabled() {
            return;
        }
        thread::scope(|scope| {
            for slot in &self.sessions {
                let launch = &launch;
                scope.spawn(move || {
                    if let Some(mut session) = free(slot)
                        && session.is_none()
                    {
                        *session = self.start(launch);
                    }
                });
            }
        });
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
        let mut guard = self.take()?;
        if guard.is_none() {
            *guard = self.start(launch);
        }
        let session = guard.as_mut()?;
        let asked = session.ask(&json!({ "cmd": command, "env": session.base }), timeout);
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

    fn take(&self) -> Option<Slot<'_>> {
        let mut unstarted = None;
        for slot in &self.sessions {
            if let Some(guard) = free(slot) {
                if guard.is_some() {
                    return Some(guard);
                }
                unstarted.get_or_insert(guard);
            }
        }
        unstarted
    }

    fn start(&self, launch: impl FnOnce() -> Result<Launch, String>) -> Option<Session> {
        let spawner = self.spawner.get_or_init(Spawner::new);
        match launch().and_then(|launch| Session::start(&launch, spawner)) {
            Ok(session) => Some(session),
            Err(reason) => {
                if self.enabled.swap(false, Ordering::Relaxed) {
                    eprintln!("[LEAN] warm Lean unavailable, checking cold: {reason}");
                }
                None
            }
        }
    }
}

fn free(slot: &Mutex<Option<Session>>) -> Option<Slot<'_>> {
    match slot.try_lock() {
        Ok(guard) => Some(guard),
        Err(TryLockError::Poisoned(poisoned)) => Some(poisoned.into_inner()),
        Err(TryLockError::WouldBlock) => None,
    }
}

/// How many warm Leans `FORMAL_WARM` asks for: a count, `off` for none, and one
/// when it is unset or says anything else.
#[must_use]
pub fn processes(env: &Env) -> usize {
    let Some(value) = env.get("FORMAL_WARM") else {
        return 1;
    };
    if OFF.contains(&value.to_lowercase().as_str()) {
        return 0;
    }
    value.parse().unwrap_or(1)
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
                "#exit",
            ] {
                let code = format!("import Mathlib\n{code}\n");
                assert_eq!(warm_command(&code), None, "{code}");
            }
        }
    }

    #[test]
    fn one_warm_lean_unless_told_otherwise() {
        assert_eq!(processes(&Env::from_pairs::<&str, &str>([])), 1);
        assert_eq!(processes(&Env::from_pairs([("FORMAL_WARM", "on")])), 1);
        assert_eq!(processes(&Env::from_pairs([("FORMAL_WARM", "3")])), 3);
        for value in ["off", "OFF", "0", "false", "none"] {
            assert_eq!(
                processes(&Env::from_pairs([("FORMAL_WARM", value)])),
                0,
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
            let warm = Warm::new(1);
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
            let warm = Warm::new(1);
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
            let warm = Warm::new(1);
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
            let warm = Warm::new(1);
            let _held = warm.sessions[0].lock().expect("an unpoisoned lock");
            assert!(warm.check("ok", SECOND, || Ok(fake())).is_none());
        }

        #[test]
        fn a_second_lean_takes_the_check_the_first_is_too_busy_for() {
            let warm = Warm::new(2);
            replied(warm.check("ok", SECOND, || Ok(fake())));
            let _held = warm.sessions[0].lock().expect("an unpoisoned lock");
            replied(warm.check("ok", SECOND, || Ok(fake())));
            assert!(
                warm.sessions[1]
                    .lock()
                    .expect("an unpoisoned lock")
                    .is_some()
            );
        }

        #[test]
        fn a_running_lean_is_preferred_to_starting_another() {
            let warm = Warm::new(3);
            replied(warm.check("ok", SECOND, || Ok(fake())));
            replied(warm.check("ok", SECOND, || panic!("one is already running")));
        }

        #[test]
        fn a_lean_outlives_the_thread_that_asked_for_it() {
            if !Path::new("/usr/bin/setpriv").is_file() {
                return;
            }
            let dies_with_its_parent = || {
                let mut launch = fake();
                let mut argv: Vec<OsString> = ["/usr/bin/setpriv", "--pdeathsig", "KILL", "--"]
                    .map(OsString::from)
                    .into();
                argv.append(&mut launch.argv);
                launch.argv = argv;
                Ok(launch)
            };
            let warm = Warm::new(1);
            thread::scope(|scope| {
                scope.spawn(|| warm.warm_up(dies_with_its_parent));
            });
            thread::sleep(Duration::from_millis(200));
            replied(warm.check("ok", SECOND, || {
                panic!("the first one should still be running")
            }));
        }

        #[test]
        fn warming_up_starts_every_lean_at_once() {
            let warm = Warm::new(3);
            warm.warm_up(|| Ok(fake()));
            for slot in &warm.sessions {
                assert!(slot.lock().expect("an unpoisoned lock").is_some());
            }
        }

        #[test]
        fn a_session_is_replaced_after_its_quota_of_commands() {
            let mut warm = Warm::new(1);
            warm.max_commands = 2;
            replied(warm.check("ok", SECOND, || Ok(fake())));
            replied(warm.check("ok", SECOND, || Ok(fake())));
            assert!(
                warm.sessions[0]
                    .lock()
                    .expect("an unpoisoned lock")
                    .is_none()
            );
        }

        #[test]
        fn a_launch_that_fails_turns_warm_checking_off() {
            let warm = Warm::new(1);
            assert!(
                warm.check("ok", SECOND, || Err("no REPL".to_string()))
                    .is_none()
            );
            assert!(!warm.enabled());
            assert!(warm.check("ok", SECOND, || Ok(fake())).is_none());
        }

        #[test]
        fn switched_off_it_never_launches() {
            let warm = Warm::new(0);
            assert!(
                warm.check("ok", SECOND, || panic!("nothing to launch"))
                    .is_none()
            );
        }
    }
}
