//! Actually invoking Lean.
//!
//! One proof, one file, one process, confined. The parts worth naming separately
//! are the timeout — a Lean run that will not finish has to be killed rather than
//! waited on — and the reading of `lean --json`, which reports a failure the same
//! way whether the proof is wrong or the toolchain is missing.

use std::{
    collections::BTreeMap,
    ffi::OsString,
    io::{
        Read,
        Write,
    },
    path::Path,
    process::{
        Command,
        Stdio,
    },
    sync::{
        OnceLock,
        atomic::{
            AtomicBool,
            Ordering,
        },
    },
    thread,
    time::{
        Duration,
        Instant,
    },
};

use formal_core::pystr;
use tempfile::Builder;

use crate::{
    paths::Paths,
    sandbox::Sandbox,
    toolchain::Toolchain,
    verifier::{
        BatchEntry,
        LeanError,
        LeanResult,
        sweep_stale_temps,
    },
};

/// How long a Lean run gets before it is killed, unless `LEAN_TIMEOUT` says otherwise.
const DEFAULT_TIMEOUT: Duration = Duration::from_mins(2);

/// How long `lake env env` gets to report the environment it manages.
const LEAN_ENV_TIMEOUT: Duration = Duration::from_secs(30);

/// How often a running Lean is asked whether it has finished.
const POLL: Duration = Duration::from_millis(20);

/// The pseudo-error that means the proof is incomplete rather than wrong.
const SORRY_DECLARATION: &str = "declaration uses 'sorry'";

/// What a finished, killed or unstartable process left behind.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Captured {
    /// The exit status, absent when the process was killed or never started.
    pub code: Option<i32>,
    /// Everything it wrote to stdout.
    pub stdout: String,
    /// Everything it wrote to stderr.
    pub stderr: String,
    /// Whether it was killed for running past its deadline.
    pub timed_out: bool,
}

/// Run a command to completion, or kill it when the deadline passes.
///
/// Both pipes are drained on their own threads. A Lean run producing more output
/// than a pipe buffer holds would otherwise block forever on a write while this
/// side blocks forever on a wait, and the timeout would be the only thing that
/// ever ended it.
///
/// # Errors
///
/// Whatever the operating system said when the process could not be started.
pub fn run_command(
    argv: &[OsString],
    cwd: &Path,
    env: &BTreeMap<OsString, OsString>,
    timeout: Duration,
) -> std::io::Result<Captured> {
    let (program, rest) = argv.split_first().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "a command with nothing to run",
        )
    })?;
    let mut child = Command::new(program)
        .args(rest)
        .current_dir(cwd)
        .env_clear()
        .envs(env)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let missing = || std::io::Error::other("a pipe the child was given did not exist");
    let mut out_pipe = child.stdout.take().ok_or_else(missing)?;
    let mut err_pipe = child.stderr.take().ok_or_else(missing)?;
    let readers = thread::scope(|scope| {
        let out = scope.spawn(move || {
            let mut buffer = Vec::new();
            let _ = out_pipe.read_to_end(&mut buffer);
            buffer
        });
        let err = scope.spawn(move || {
            let mut buffer = Vec::new();
            let _ = err_pipe.read_to_end(&mut buffer);
            buffer
        });

        let started = Instant::now();
        let mut timed_out = false;
        let code = loop {
            match child.try_wait() {
                Ok(Some(status)) => break status.code(),
                Err(_) => break None,
                Ok(None) => {}
            }
            if started.elapsed() >= timeout {
                let _ = child.kill();
                let _ = child.wait();
                timed_out = true;
                break None;
            }
            thread::sleep(POLL);
        };
        (
            code,
            timed_out,
            out.join().unwrap_or_default(),
            err.join().unwrap_or_default(),
        )
    });

    let (code, timed_out, stdout, stderr) = readers;
    Ok(Captured {
        code,
        stdout: String::from_utf8_lossy(&stdout).into_owned(),
        stderr: String::from_utf8_lossy(&stderr).into_owned(),
        timed_out,
    })
}

/// Read what `lean --json` printed into a verdict.
///
/// A line that is not a JSON object is output and nothing more — Lean prints
/// plenty of those, and Python read one as a diagnostic and raised.
#[must_use]
pub fn parse_output(captured: &Captured) -> LeanResult {
    let lines = pystr::splitlines(&captured.stdout);
    let messages: Vec<LeanError> = lines
        .iter()
        .filter_map(|line| serde_json::from_str::<LeanError>(line).ok())
        .collect();

    let mut errors: Vec<LeanError> = messages
        .iter()
        .filter(|message| message.severity == "error" && !message.data.contains(SORRY_DECLARATION))
        .cloned()
        .collect();

    // A sorry is a warning to Lean and a failure here: the proof has a hole in it.
    // Appended after the errors, so the first error stays the first thing Lean said.
    errors.extend(
        messages
            .iter()
            .filter(|message| message.severity == "warning" && message.data.contains("sorry"))
            .map(|message| LeanError {
                severity: "error".to_string(),
                ..message.clone()
            }),
    );

    let mut output = lines.join("\n");
    if !captured.stderr.is_empty() {
        output.push('\n');
        output.push_str(&captured.stderr);
    }
    LeanResult {
        success: captured.code == Some(0) && errors.is_empty(),
        output,
        errors,
    }
}

fn failed(output: impl Into<String>) -> LeanResult {
    LeanResult {
        success: false,
        output: output.into(),
        errors: Vec::new(),
    }
}

/// Everything needed to run Lean, resolved once.
#[derive(Debug)]
pub struct Runner {
    paths: Paths,
    toolchain: Toolchain,
    sandbox: Sandbox,
    timeout: Duration,
    /// The environment `lake` manages, captured at first use.
    ///
    /// `lake env lean` re-invokes lake on every call just to set variables. Asking
    /// once and calling `lean` directly saves about 100ms a run. Absent means the
    /// question could not be answered and every call goes through lake instead.
    lean_env: OnceLock<Option<BTreeMap<OsString, OsString>>>,
    warned: AtomicBool,
}

impl Runner {
    /// A runner configured from the environment.
    #[must_use]
    pub fn from_env() -> Self {
        let paths = Paths::from_env();
        let toolchain = Toolchain::from_env();
        let sandbox = Sandbox::from_env(&paths, &toolchain);
        let timeout = std::env::var("LEAN_TIMEOUT")
            .ok()
            .and_then(|value| value.trim().parse::<u64>().ok())
            .map_or(DEFAULT_TIMEOUT, Duration::from_secs);
        Self::new(paths, toolchain, sandbox, timeout)
    }

    /// A runner told what to use rather than asked to find it.
    #[must_use]
    pub fn new(paths: Paths, toolchain: Toolchain, sandbox: Sandbox, timeout: Duration) -> Self {
        Self {
            paths,
            toolchain,
            sandbox,
            timeout,
            lean_env: OnceLock::new(),
            warned: AtomicBool::new(false),
        }
    }

    /// Where Lean will be run.
    #[must_use]
    pub fn paths(&self) -> &Paths {
        &self.paths
    }

    /// How the Lean process is confined.
    #[must_use]
    pub fn sandbox(&self) -> &Sandbox {
        &self.sandbox
    }

    fn lean_env(&self) -> Option<&BTreeMap<OsString, OsString>> {
        self.lean_env
            .get_or_init(|| {
                let lake = self.toolchain.which("lake")?;
                let argv = vec![lake.into(), OsString::from("env"), OsString::from("env")];
                let captured = run_command(
                    &argv,
                    &self.paths.lean_project_dir,
                    &self.toolchain.env(),
                    LEAN_ENV_TIMEOUT,
                )
                .ok()?;
                if captured.code != Some(0) {
                    return None;
                }
                let mut env = self.toolchain.env();
                for line in pystr::splitlines(&captured.stdout) {
                    if let Some((key, value)) = line.split_once('=') {
                        env.insert(OsString::from(key), OsString::from(value));
                    }
                }
                Some(env)
            })
            .as_ref()
    }

    /// The command that checks `path`, going straight to `lean` when lake has
    /// already been asked what it would have set.
    fn lean_command(&self, path: &Path) -> (Vec<OsString>, BTreeMap<OsString, OsString>) {
        let json = OsString::from("--json");
        if let Some(env) = self.lean_env() {
            let lean = self
                .toolchain
                .which("lean")
                .map_or_else(|| OsString::from("lean"), Into::into);
            return (vec![lean, json, path.into()], env.clone());
        }
        let lake = self
            .toolchain
            .which("lake")
            .map_or_else(|| OsString::from("lake"), Into::into);
        (
            vec![lake, "env".into(), "lean".into(), json, path.into()],
            self.toolchain.env(),
        )
    }

    /// Write `lean_code` to a scratch file and check it.
    ///
    /// Every way of failing to run Lean at all — no toolchain, no sandbox where
    /// one was required, an unwritable project — comes back as a failure carrying
    /// no diagnostics, which is what tells a batch it cannot attribute anything
    /// and a caller that Lean never gave a verdict.
    pub fn verify(&self, lean_code: &str, timeout: Option<Duration>) -> LeanResult {
        if lean_code.trim().is_empty() {
            return failed("Empty Lean code");
        }

        let verify_dir = self.paths.verify_dir();
        if let Err(e) = std::fs::create_dir_all(&verify_dir) {
            return failed(format!("Could not prepare {}: {e}", verify_dir.display()));
        }
        sweep_stale_temps(&verify_dir);

        let mut scratch = match Builder::new()
            .prefix("tmp_")
            .suffix(".lean")
            .tempfile_in(&verify_dir)
        {
            Ok(file) => file,
            Err(e) => {
                return failed(format!(
                    "Could not write a scratch file in {}: {e}",
                    verify_dir.display()
                ));
            }
        };
        if let Err(e) = scratch
            .write_all(lean_code.as_bytes())
            .and_then(|()| scratch.flush())
        {
            return failed(format!(
                "Could not write a scratch file in {}: {e}",
                verify_dir.display()
            ));
        }

        let (cmd, env) = self.lean_command(scratch.path());
        let wrapped = match self.sandbox.wrap(&cmd) {
            Ok(wrapped) => wrapped,
            Err(e) => return failed(e.to_string()),
        };
        if let Some(warning) = wrapped.warning
            && !self.warned.swap(true, Ordering::Relaxed)
        {
            eprintln!("[LEAN] {warning}");
        }

        let effective = timeout.unwrap_or(self.timeout);
        match run_command(&wrapped.argv, &self.paths.lean_project_dir, &env, effective) {
            Err(e) => failed(format!("Could not run Lean: {e}")),
            Ok(captured) if captured.timed_out => LeanResult {
                success: false,
                output: format!("Lean verification timed out after {}s", effective.as_secs()),
                errors: vec![LeanError {
                    severity: "error".to_string(),
                    data: "timeout".to_string(),
                    line: Some(0),
                    col: Some(0),
                    pos: None,
                }],
            },
            Ok(captured) => parse_output(&captured),
        }
    }

    /// Check several proofs in one invocation, paying one Mathlib import.
    ///
    /// Nothing when the batch itself could not be run, in which case the caller
    /// verifies each proof on its own.
    pub fn verify_batch(
        &self,
        entries: &mut [BatchEntry],
        timeout: Option<Duration>,
    ) -> Option<Vec<(String, LeanResult)>> {
        crate::verifier::verify_batch(entries, |source| self.verify(source, timeout))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn env() -> BTreeMap<OsString, OsString> {
        BTreeMap::from([(OsString::from("PATH"), OsString::from("/usr/bin:/bin"))])
    }

    fn sh(script: &str) -> Vec<OsString> {
        vec!["/bin/sh".into(), "-c".into(), script.into()]
    }

    mod running {
        use super::*;

        #[test]
        fn output_and_status_come_back() {
            let captured = run_command(
                &sh("echo out; echo err >&2; exit 3"),
                Path::new("/"),
                &env(),
                Duration::from_secs(10),
            )
            .expect("the shell runs");
            assert_eq!(captured.code, Some(3));
            assert_eq!(captured.stdout, "out\n");
            assert_eq!(captured.stderr, "err\n");
            assert!(!captured.timed_out);
        }

        #[test]
        fn a_process_that_overruns_is_killed_and_says_so() {
            let started = Instant::now();
            let captured = run_command(
                &sh("sleep 30"),
                Path::new("/"),
                &env(),
                Duration::from_millis(200),
            )
            .expect("the shell runs");
            assert!(captured.timed_out);
            assert!(captured.code.is_none());
            assert!(
                started.elapsed() < Duration::from_secs(5),
                "{:?}",
                started.elapsed()
            );
        }

        #[test]
        fn more_output_than_a_pipe_buffer_holds_does_not_deadlock() {
            let captured = run_command(
                &sh("head -c 1000000 /dev/zero | tr '\\0' 'x'"),
                Path::new("/"),
                &env(),
                Duration::from_secs(30),
            )
            .expect("the shell runs");
            assert_eq!(captured.stdout.len(), 1_000_000);
            assert!(!captured.timed_out);
        }

        #[test]
        fn the_environment_is_replaced_rather_than_added_to() {
            let captured = run_command(
                &sh("echo ${HOME:-unset}"),
                Path::new("/"),
                &env(),
                Duration::from_secs(10),
            )
            .expect("the shell runs");
            assert_eq!(captured.stdout, "unset\n");
        }

        #[test]
        fn a_command_that_does_not_exist_is_an_error_and_not_a_verdict() {
            let argv = vec![OsString::from("/nonexistent/lean")];
            assert!(run_command(&argv, Path::new("/"), &env(), Duration::from_secs(10)).is_err());
        }

        #[test]
        fn nothing_to_run_is_refused() {
            assert!(run_command(&[], Path::new("/"), &env(), Duration::from_secs(10)).is_err());
        }
    }

    mod reading {
        use super::*;

        fn message(severity: &str, data: &str, line: u32) -> String {
            serde_json::json!({
                "severity": severity,
                "data": data,
                "pos": { "line": line, "column": 0 },
            })
            .to_string()
        }

        fn captured(code: i32, stdout: &str) -> Captured {
            Captured {
                code: Some(code),
                stdout: stdout.to_string(),
                stderr: String::new(),
                timed_out: false,
            }
        }

        #[test]
        fn a_clean_run_succeeds() {
            let result = parse_output(&captured(0, ""));
            assert!(result.success);
            assert!(result.errors.is_empty());
        }

        #[test]
        fn an_error_is_a_failure_and_keeps_its_position() {
            let result = parse_output(&captured(1, &message("error", "unsolved goals", 12)));
            assert!(!result.success);
            assert_eq!(result.errors.len(), 1);
            assert_eq!(result.errors[0].position(), (Some(12), Some(0)));
        }

        #[test]
        fn the_sorry_pseudo_error_is_not_an_error() {
            let result = parse_output(&captured(
                0,
                &message("error", "declaration uses 'sorry'", 1),
            ));
            assert!(result.errors.is_empty());
            assert!(result.success);
        }

        #[test]
        fn a_sorry_warning_is_promoted_so_a_hole_is_not_a_pass() {
            let result = parse_output(&captured(
                0,
                &message("warning", "declaration uses sorry", 4),
            ));
            assert!(!result.success);
            assert_eq!(result.errors.len(), 1);
            assert_eq!(result.errors[0].severity, "error");
        }

        #[test]
        fn a_promoted_warning_comes_after_the_real_errors() {
            let stdout = format!(
                "{}\n{}",
                message("warning", "declaration uses sorry", 9),
                message("error", "unsolved goals", 2)
            );
            let result = parse_output(&captured(1, &stdout));
            assert_eq!(result.errors[0].data, "unsolved goals");
            assert_eq!(result.errors[1].data, "declaration uses sorry");
        }

        #[test]
        fn a_line_that_is_not_json_is_output_and_nothing_more() {
            let stdout = format!("some prose Lean printed\n{}", message("error", "boom", 1));
            let result = parse_output(&captured(1, &stdout));
            assert_eq!(result.errors.len(), 1);
            assert!(result.output.starts_with("some prose Lean printed\n"));
        }

        #[test]
        fn a_json_line_that_is_not_an_object_is_not_a_diagnostic() {
            let result = parse_output(&captured(0, "5\n[1, 2]\n\"a string\""));
            assert!(result.errors.is_empty());
            assert!(result.success);
        }

        #[test]
        fn a_nonzero_exit_with_nothing_to_report_is_still_a_failure() {
            assert!(!parse_output(&captured(1, "")).success);
        }

        #[test]
        fn stderr_is_appended_to_the_output() {
            let result = parse_output(&Captured {
                code: Some(1),
                stdout: "one".to_string(),
                stderr: "two".to_string(),
                timed_out: false,
            });
            assert_eq!(result.output, "one\ntwo");
        }
    }

    mod verifying {
        use std::path::PathBuf;

        use tempfile::TempDir;

        use super::*;
        use crate::sandbox::Mode;

        fn runner(home: &Path) -> Runner {
            let paths = Paths::under(home.to_path_buf());
            let toolchain = Toolchain::new(
                PathBuf::from("/nonexistent/elan"),
                &OsString::from("/nonexistent"),
            );
            let sandbox = Sandbox::new(Mode::Off, None, &paths, &toolchain);
            Runner::new(paths, toolchain, sandbox, Duration::from_secs(5))
        }

        #[test]
        fn empty_code_never_reaches_lean() {
            let dir = TempDir::new().expect("a temporary directory");
            let result = runner(dir.path()).verify("   \n ", None);
            assert_eq!(result.output, "Empty Lean code");
            assert!(!result.success);
            assert!(!dir.path().join("lean_project/Verify").exists());
        }

        #[test]
        fn a_missing_toolchain_is_a_failure_with_no_diagnostics() {
            let dir = TempDir::new().expect("a temporary directory");
            let result = runner(dir.path()).verify("theorem t : True := trivial", None);
            assert!(!result.success);
            assert!(result.errors.is_empty(), "{:?}", result.errors);
            assert!(
                result.output.contains("Could not run Lean"),
                "{}",
                result.output
            );
        }

        #[test]
        fn the_scratch_file_does_not_outlive_the_run() {
            let dir = TempDir::new().expect("a temporary directory");
            runner(dir.path()).verify("theorem t : True := trivial", None);
            let left = std::fs::read_dir(dir.path().join("lean_project/Verify"))
                .expect("the directory was made")
                .count();
            assert_eq!(left, 0);
        }

        #[test]
        fn a_sandbox_that_was_required_and_is_missing_stops_the_run() {
            let dir = TempDir::new().expect("a temporary directory");
            let paths = Paths::under(dir.path().to_path_buf());
            let toolchain = Toolchain::new(
                PathBuf::from("/nonexistent/elan"),
                &OsString::from("/usr/bin"),
            );
            let sandbox = Sandbox::new(Mode::Required, None, &paths, &toolchain);
            let runner = Runner::new(paths, toolchain, sandbox, Duration::from_secs(5));
            let result = runner.verify("theorem t : True := trivial", None);
            assert!(!result.success);
            assert!(
                result.output.contains("bubblewrap is not installed"),
                "{}",
                result.output
            );
        }
    }
}
