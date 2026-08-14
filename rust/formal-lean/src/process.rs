//! Reaching the HTTP server, and starting it when nothing is listening.
//!
//! An agent invoking formal from an arbitrary directory cannot assume a server is
//! up, and cannot run one in the foreground — a command that never returns is a
//! command it cannot use. Both are the same problem: starting the server has to be
//! safe to do unconditionally, and it has to come back.

use std::{
    fs,
    io::{
        BufRead,
        BufReader,
        Write,
    },
    net::{
        SocketAddr,
        TcpStream,
        ToSocketAddrs,
    },
    os::unix::process::CommandExt,
    path::PathBuf,
    process::{
        Command,
        Stdio,
    },
    thread,
    time::{
        Duration,
        Instant,
    },
};

use thiserror::Error;

use crate::{
    env::Env,
    paths::Paths,
};

/// Where formal listens when nothing says otherwise.
pub const DEFAULT_HOST: &str = "127.0.0.1";

/// The port formal listens on when nothing says otherwise.
pub const DEFAULT_PORT: u16 = 1337;

/// How long to give a health check before calling it a no.
const HEALTH_TIMEOUT: Duration = Duration::from_millis(500);

/// How long to wait for a server that was just started to answer.
const START_TIMEOUT: Duration = Duration::from_secs(30);

/// How long to wait for a server that was asked to stop.
const STOP_TIMEOUT: Duration = Duration::from_secs(10);

/// How often to ask again while waiting.
const POLL: Duration = Duration::from_millis(200);

/// Starting or stopping the server did not work.
#[derive(Debug, Error)]
pub enum ControlError {
    /// The server could not be launched at all.
    #[error("could not start the server: {0}")]
    Unstartable(#[from] std::io::Error),

    /// It started and then stopped, which the log will explain.
    #[error("server exited immediately (code {code}) — see {log}")]
    ExitedImmediately {
        /// What it exited with.
        code: i32,
        /// Where it said why.
        log: PathBuf,
    },

    /// It is running but not answering.
    #[error("server did not answer on {url} within {}s — see {log}", timeout.as_secs())]
    NeverAnswered {
        /// Where it was expected.
        url: String,
        /// How long it was given.
        timeout: Duration,
        /// Where it may have said why.
        log: PathBuf,
    },
}

/// Where the server is, or should be.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Endpoint {
    /// The interface to listen on.
    pub host: String,
    /// The port to listen on.
    pub port: u16,
}

impl Default for Endpoint {
    fn default() -> Self {
        Self {
            host: DEFAULT_HOST.to_string(),
            port: DEFAULT_PORT,
        }
    }
}

impl Endpoint {
    /// Where configuration says the server is.
    #[must_use]
    pub fn resolve(env: &Env) -> Self {
        Self {
            host: env.get("FORMAL_HOST").unwrap_or(DEFAULT_HOST).to_string(),
            port: env.number("FORMAL_PORT").unwrap_or(DEFAULT_PORT),
        }
    }

    /// The base URL, as it should be printed and fetched.
    #[must_use]
    pub fn url(&self) -> String {
        format!("http://{}:{}", self.host, self.port)
    }

    fn address(&self) -> Option<SocketAddr> {
        (self.host.as_str(), self.port)
            .to_socket_addrs()
            .ok()?
            .next()
    }

    /// Whether something answers `/health`, which is the only claim worth making.
    ///
    /// One fixed GET over one socket. formal is a localhost service and this is
    /// the whole of its use for a client, so it does not carry one.
    #[must_use]
    pub fn is_running(&self) -> bool {
        self.health().unwrap_or(false)
    }

    fn health(&self) -> std::io::Result<bool> {
        let mut stream = TcpStream::connect_timeout(
            &self
                .address()
                .ok_or_else(|| std::io::Error::other("no such address"))?,
            HEALTH_TIMEOUT,
        )?;
        stream.set_read_timeout(Some(HEALTH_TIMEOUT))?;
        stream.set_write_timeout(Some(HEALTH_TIMEOUT))?;
        write!(
            stream,
            "GET /health HTTP/1.1\r\nHost: {}\r\nConnection: close\r\n\r\n",
            self.host
        )?;
        stream.flush()?;

        let mut status = String::new();
        BufReader::new(stream).read_line(&mut status)?;
        Ok(status.starts_with("HTTP/1.1 200") || status.starts_with("HTTP/1.0 200"))
    }
}

/// The server as something to start, stop and ask after.
#[derive(Clone, Debug)]
pub struct Server {
    /// Where it listens.
    pub endpoint: Endpoint,
    home: PathBuf,
}

impl Server {
    /// The server at `endpoint`, keeping its pid and log under `paths`.
    #[must_use]
    pub fn new(endpoint: Endpoint, paths: &Paths) -> Self {
        Self {
            endpoint,
            home: paths.formal_home.clone(),
        }
    }

    /// Where the pid of a server started in the background is recorded.
    #[must_use]
    pub fn pid_file(&self) -> PathBuf {
        self.home.join("server.pid")
    }

    /// Where a server started in the background writes its output.
    #[must_use]
    pub fn log_file(&self) -> PathBuf {
        self.home.join("server.log")
    }

    /// Start the server unless it is already up, and return once it answers.
    ///
    /// Idempotent on purpose: a caller that cannot see the machine's process list
    /// should be able to run this before every request without thinking about it.
    ///
    /// `command` is what to run — this crate does not know what the binary is
    /// called, and a test should not have to launch the real one.
    ///
    /// # Errors
    ///
    /// [`ControlError`] when the process will not start, stops at once, or never
    /// answers.
    pub fn start(
        &self,
        mut command: Command,
        wait: Option<Duration>,
    ) -> Result<String, ControlError> {
        if self.endpoint.is_running() {
            return Ok(self.endpoint.url());
        }

        fs::create_dir_all(&self.home)?;
        let log = fs::File::options()
            .append(true)
            .create(true)
            .open(self.log_file())?;

        // A new process group, so closing the shell that ran this does not take the
        // server with it. Python called setsid; the server itself declines SIGHUP,
        // which gets to the same place without reaching for unsafe.
        let mut child = command
            .stdin(Stdio::null())
            .stdout(Stdio::from(log.try_clone()?))
            .stderr(Stdio::from(log))
            .process_group(0)
            .spawn()?;
        fs::write(self.pid_file(), child.id().to_string())?;

        let wait = wait.unwrap_or(START_TIMEOUT);
        let deadline = Instant::now() + wait;
        while Instant::now() < deadline {
            if self.endpoint.is_running() {
                return Ok(self.endpoint.url());
            }
            if let Ok(Some(status)) = child.try_wait() {
                return Err(ControlError::ExitedImmediately {
                    code: status.code().unwrap_or(-1),
                    log: self.log_file(),
                });
            }
            thread::sleep(POLL);
        }
        Err(ControlError::NeverAnswered {
            url: self.endpoint.url(),
            timeout: wait,
            log: self.log_file(),
        })
    }

    fn recorded_pid(&self) -> Option<u32> {
        fs::read_to_string(self.pid_file())
            .ok()?
            .trim()
            .parse()
            .ok()
    }

    /// Guard against a stale pid file naming a process the system has since reused.
    fn is_ours(pid: u32) -> bool {
        fs::read(format!("/proc/{pid}/cmdline")).map_or(true, |cmdline| {
            String::from_utf8_lossy(&cmdline).contains("formal")
        })
    }

    /// Stop a server we started. False when there was nothing of ours to stop.
    #[must_use]
    pub fn stop(&self, wait: Option<Duration>) -> bool {
        let Some(pid) = self.recorded_pid().filter(|pid| Self::is_ours(*pid)) else {
            let _ = fs::remove_file(self.pid_file());
            return false;
        };

        if !terminate(pid) {
            let _ = fs::remove_file(self.pid_file());
            return false;
        }

        let deadline = Instant::now() + wait.unwrap_or(STOP_TIMEOUT);
        while Instant::now() < deadline {
            if !self.endpoint.is_running() {
                let _ = fs::remove_file(self.pid_file());
                return true;
            }
            thread::sleep(POLL);
        }
        false
    }
}

/// Ask a process to stop, reporting whether there was one to ask.
///
/// `kill` rather than a signal crate: sending SIGTERM is one command, and the
/// alternative is a dependency for it.
fn terminate(pid: u32) -> bool {
    Command::new("kill")
        .arg("-TERM")
        .arg(pid.to_string())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

#[cfg(test)]
mod tests {
    use tempfile::TempDir;

    use super::*;

    fn server(dir: &TempDir, port: u16) -> Server {
        Server::new(
            Endpoint {
                host: DEFAULT_HOST.to_string(),
                port,
            },
            &Paths::under(dir.path().to_path_buf()),
        )
    }

    #[test]
    fn the_defaults_are_what_python_listened_on() {
        let endpoint = Endpoint::default();
        assert_eq!(endpoint.url(), "http://127.0.0.1:1337");
    }

    #[test]
    fn configuration_moves_the_endpoint() {
        let endpoint = Endpoint::resolve(&Env::from_pairs([
            ("FORMAL_HOST", "0.0.0.0"),
            ("FORMAL_PORT", "9001"),
        ]));
        assert_eq!(endpoint.url(), "http://0.0.0.0:9001");
    }

    #[test]
    fn a_port_that_is_not_a_number_leaves_the_default() {
        let endpoint = Endpoint::resolve(&Env::from_pairs([("FORMAL_PORT", "soon")]));
        assert_eq!(endpoint.port, DEFAULT_PORT);
    }

    #[test]
    fn nothing_listening_is_not_running() {
        let endpoint = Endpoint {
            host: DEFAULT_HOST.to_string(),
            port: 1,
        };
        assert!(!endpoint.is_running());
    }

    #[test]
    fn the_pid_and_the_log_sit_under_the_home() {
        let dir = TempDir::new().expect("a temporary directory");
        let server = server(&dir, 9999);
        assert_eq!(server.pid_file(), dir.path().join("server.pid"));
        assert_eq!(server.log_file(), dir.path().join("server.log"));
    }

    #[test]
    fn a_process_that_stops_at_once_is_reported_with_its_code() {
        let dir = TempDir::new().expect("a temporary directory");
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "exit 3"]);
        let error = server(&dir, 9998)
            .start(command, Some(Duration::from_secs(5)))
            .expect_err("it exits at once");
        assert!(
            matches!(error, ControlError::ExitedImmediately { code: 3, .. }),
            "{error}"
        );
    }

    /// A process whose command line names formal, as the real server's does.
    ///
    /// A script rather than `sh -c`: a shell running one command execs it and is
    /// replaced, so whatever the script says would not survive into the cmdline.
    fn ours(dir: &TempDir) -> Command {
        let script = dir.path().join("formal-stub");
        fs::write(&script, "#!/bin/sh\nsleep 20\n").expect("writable");
        fs::set_permissions(&script, std::os::unix::fs::PermissionsExt::from_mode(0o755))
            .expect("the mode is settable");
        Command::new(script)
    }

    #[test]
    fn a_process_that_never_answers_is_given_up_on() {
        let dir = TempDir::new().expect("a temporary directory");
        let server = server(&dir, 9997);
        let error = server
            .start(ours(&dir), Some(Duration::from_millis(400)))
            .expect_err("nothing is listening");
        assert!(
            matches!(error, ControlError::NeverAnswered { .. }),
            "{error}"
        );
        let _ = server.stop(Some(Duration::from_secs(3)));
    }

    #[test]
    fn what_was_started_is_recorded_and_can_be_stopped() {
        let dir = TempDir::new().expect("a temporary directory");
        let server = server(&dir, 9996);
        let _ = server.start(ours(&dir), Some(Duration::from_millis(300)));

        assert!(server.pid_file().is_file(), "the pid was written down");
        assert!(server.stop(Some(Duration::from_secs(3))));
        assert!(!server.pid_file().exists(), "and cleared once it was gone");
    }

    #[test]
    fn a_process_that_is_not_ours_is_left_alone() {
        let dir = TempDir::new().expect("a temporary directory");
        let server = server(&dir, 9992);
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "sleep 2"]);
        let _ = server.start(command, Some(Duration::from_millis(300)));

        assert!(
            !server.stop(Some(Duration::from_secs(1))),
            "the pid was reused by something else, so it is not ours to kill"
        );
        assert!(
            !server.pid_file().exists(),
            "and the stale record is cleared"
        );
    }

    #[test]
    fn there_is_nothing_to_stop_when_nothing_was_started() {
        let dir = TempDir::new().expect("a temporary directory");
        assert!(!server(&dir, 9995).stop(Some(Duration::from_secs(1))));
    }

    #[test]
    fn a_pid_file_naming_nothing_is_cleared_rather_than_trusted() {
        let dir = TempDir::new().expect("a temporary directory");
        let server = server(&dir, 9994);
        fs::create_dir_all(dir.path()).expect("writable");
        fs::write(server.pid_file(), "4294967290").expect("writable");
        assert!(!server.stop(Some(Duration::from_secs(1))));
        assert!(!server.pid_file().exists());
    }

    #[test]
    fn a_pid_file_that_is_not_a_pid_is_cleared() {
        let dir = TempDir::new().expect("a temporary directory");
        let server = server(&dir, 9993);
        fs::create_dir_all(dir.path()).expect("writable");
        fs::write(server.pid_file(), "not a pid").expect("writable");
        assert!(!server.stop(Some(Duration::from_secs(1))));
        assert!(!server.pid_file().exists());
    }
}
