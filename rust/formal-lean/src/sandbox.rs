//! Confinement for the Lean subprocess, which elaborates caller-authored code.
//!
//! Lean can execute arbitrary code while elaborating (`#eval`, macros,
//! `initialize`), so proofs are checked inside bubblewrap: no network, no home
//! directory, and nothing writable except the Lean project itself.

use std::{
    ffi::OsString,
    path::{
        Path,
        PathBuf,
    },
};

use thiserror::Error;

use crate::{
    env::Env,
    paths::{
        Paths,
        home_dir,
    },
    toolchain::Toolchain,
};

/// The spellings of `FORMAL_SANDBOX` that mean "do not confine".
const OFF: [&str; 5] = ["off", "none", "0", "false", ""];

/// Sandboxing was asked for by name and cannot be provided.
#[derive(Clone, Debug, Error)]
#[error("FORMAL_SANDBOX=bwrap but bubblewrap is not installed")]
pub struct NotInstalled;

/// What `FORMAL_SANDBOX` asked for.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mode {
    /// Confine if bubblewrap is there, and say so once if it is not.
    Auto,
    /// Confine or refuse to run.
    Required,
    /// Do not confine.
    Off,
}

impl Mode {
    /// Read the mode from the value of `FORMAL_SANDBOX`, defaulting to `Auto`.
    #[must_use]
    pub fn parse(value: Option<&str>) -> Self {
        let value = value.unwrap_or("auto").trim().to_lowercase();
        if OFF.contains(&value.as_str()) {
            return Self::Off;
        }
        if value == "bwrap" {
            Self::Required
        } else {
            Self::Auto
        }
    }

    /// The mode this process was started in.
    #[must_use]
    pub fn from_env() -> Self {
        Self::resolve(&Env::process())
    }

    /// The same, from configuration that was collected rather than read.
    #[must_use]
    pub fn resolve(env: &Env) -> Self {
        Self::parse(env.get("FORMAL_SANDBOX"))
    }
}

/// A command, confined or knowingly not.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Wrapped {
    /// What to actually run.
    pub argv: Vec<OsString>,
    /// Why it is running unconfined, when that was not what was asked for.
    ///
    /// Python kept a module-level flag so this was logged once per process. The
    /// decision of how often to say it belongs to whoever holds the log, not here.
    pub warning: Option<&'static str>,
}

/// How Lean is confined, and everything the confinement needs to name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sandbox {
    mode: Mode,
    bwrap: Option<PathBuf>,
    home: PathBuf,
    elan_home: PathBuf,
    lean_project_dir: PathBuf,
}

impl Sandbox {
    /// The sandbox this process would use.
    #[must_use]
    pub fn from_env(paths: &Paths, toolchain: &Toolchain) -> Self {
        Self::resolve(&Env::process(), paths, toolchain)
    }

    /// The same, from configuration that was collected rather than read.
    #[must_use]
    pub fn resolve(env: &Env, paths: &Paths, toolchain: &Toolchain) -> Self {
        Self::new(Mode::resolve(env), which_bwrap(), paths, toolchain)
    }

    /// The same, for a stated mode and a stated bubblewrap.
    #[must_use]
    pub fn new(mode: Mode, bwrap: Option<PathBuf>, paths: &Paths, toolchain: &Toolchain) -> Self {
        Self {
            mode,
            bwrap,
            home: home_dir(),
            elan_home: toolchain.elan_home.clone(),
            lean_project_dir: paths.lean_project_dir.clone(),
        }
    }

    /// How to describe the confinement in `formal status`.
    #[must_use]
    pub fn describe(&self) -> String {
        match (self.mode, self.bwrap.is_some()) {
            (Mode::Off, _) => "off (FORMAL_SANDBOX)".to_string(),
            (_, false) => "unavailable — install bubblewrap".to_string(),
            (_, true) => "bubblewrap".to_string(),
        }
    }

    /// Wrap `cmd` in bubblewrap, or hand it back when sandboxing is unavailable.
    ///
    /// # Errors
    ///
    /// [`NotInstalled`] when the mode names bubblewrap and there is none. Auto
    /// mode reports the same fact as a warning and runs anyway, which is the
    /// choice Python made and the reason the warning is carried out of here.
    pub fn wrap<S: AsRef<std::ffi::OsStr>>(&self, cmd: &[S]) -> Result<Wrapped, NotInstalled> {
        let argv: Vec<OsString> = cmd
            .iter()
            .map(|part| part.as_ref().to_os_string())
            .collect();
        if self.mode == Mode::Off {
            return Ok(Wrapped {
                argv,
                warning: None,
            });
        }
        let Some(bwrap) = &self.bwrap else {
            if self.mode == Mode::Required {
                return Err(NotInstalled);
            }
            return Ok(Wrapped {
                argv,
                warning: Some(
                    "bubblewrap not found — running Lean unsandboxed. Install bubblewrap, or set \
                     FORMAL_SANDBOX=off to silence this.",
                ),
            });
        };

        let mut wrapped: Vec<OsString> = vec![bwrap.into()];
        let mut push = |args: &[&dyn AsRef<Path>]| {
            wrapped.extend(args.iter().map(|a| a.as_ref().as_os_str().into()));
        };
        push(&[&"--ro-bind", &"/", &"/"]);
        push(&[&"--dev", &"/dev"]);
        push(&[&"--proc", &"/proc"]);
        push(&[&"--tmpfs", &"/tmp"]);
        // The home tmpfs comes before the project bind, so a project inside the
        // home directory is masked and then restored rather than the other way round.
        push(&[&"--tmpfs", &self.home]);
        push(&[&"--ro-bind-try", &self.elan_home, &self.elan_home]);
        push(&[&"--bind", &self.lean_project_dir, &self.lean_project_dir]);
        push(&[&"--chdir", &self.lean_project_dir]);
        for flag in [
            "--unshare-net",
            "--unshare-pid",
            "--unshare-ipc",
            "--unshare-uts",
            "--new-session",
            "--die-with-parent",
            "--",
        ] {
            wrapped.push(flag.into());
        }
        wrapped.extend(argv);
        Ok(Wrapped {
            argv: wrapped,
            warning: None,
        })
    }
}

fn which_bwrap() -> Option<PathBuf> {
    std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default())
        .map(|dir| dir.join("bwrap"))
        .find(|candidate| candidate.is_file())
}

#[cfg(test)]
mod tests {
    use std::ffi::OsStr;

    use super::*;

    const CMD: [&str; 3] = ["lean", "--json", "/lean_project/Verify/tmp_x.lean"];

    fn sandbox(mode: Mode, bwrap: Option<&str>) -> Sandbox {
        let paths = Paths::under(PathBuf::from("/srv/formal"));
        let toolchain = Toolchain::new(PathBuf::from("/srv/elan"), &OsString::from("/usr/bin"));
        Sandbox::new(mode, bwrap.map(PathBuf::from), &paths, &toolchain)
    }

    fn wrapped() -> Vec<OsString> {
        sandbox(Mode::Auto, Some("/usr/bin/bwrap"))
            .wrap(&CMD)
            .expect("bubblewrap is available")
            .argv
    }

    fn contains(argv: &[OsString], run: &[&str]) -> bool {
        argv.windows(run.len())
            .any(|window| window.iter().eq(run.iter().map(OsStr::new)))
    }

    #[test]
    fn every_spelling_of_off_means_off() {
        for value in ["off", "none", "0", "false", "OFF", " off "] {
            assert_eq!(Mode::parse(Some(value)), Mode::Off, "{value}");
        }
    }

    #[test]
    fn the_default_is_auto() {
        assert_eq!(Mode::parse(None), Mode::Auto);
        assert_eq!(Mode::parse(Some("auto")), Mode::Auto);
    }

    #[test]
    fn disabled_returns_the_command_unchanged() {
        let result = sandbox(Mode::Off, Some("/usr/bin/bwrap"))
            .wrap(&CMD)
            .expect("off never fails");
        assert_eq!(result.argv, CMD.map(OsString::from));
        assert!(result.warning.is_none());
    }

    #[test]
    fn auto_without_bwrap_runs_unwrapped_and_says_so() {
        let result = sandbox(Mode::Auto, None)
            .wrap(&CMD)
            .expect("auto tolerates the absence");
        assert_eq!(result.argv, CMD.map(OsString::from));
        assert!(result.warning.is_some_and(|w| w.contains("unsandboxed")));
    }

    #[test]
    fn asking_for_bwrap_by_name_without_bwrap_is_refused() {
        let error = sandbox(Mode::Required, None)
            .wrap(&CMD)
            .expect_err("it is refused");
        assert!(error.to_string().contains("not installed"), "{error}");
    }

    #[test]
    fn the_command_is_preserved_after_the_separator() {
        let argv = wrapped();
        let separator = argv
            .iter()
            .position(|part| part == "--")
            .expect("a separator");
        assert_eq!(argv[separator + 1..], CMD.map(OsString::from));
    }

    #[test]
    fn network_and_namespaces_are_unshared() {
        let argv = wrapped();
        for flag in [
            "--unshare-net",
            "--unshare-pid",
            "--unshare-ipc",
            "--unshare-uts",
        ] {
            assert!(argv.iter().any(|part| part == flag), "{flag}");
        }
    }

    #[test]
    fn it_dies_with_its_parent_and_detaches_the_terminal() {
        let argv = wrapped();
        for flag in ["--die-with-parent", "--new-session"] {
            assert!(argv.iter().any(|part| part == flag), "{flag}");
        }
    }

    #[test]
    fn root_is_bound_read_only_and_home_is_masked() {
        let argv = wrapped();
        assert!(contains(&argv, &["--ro-bind", "/", "/"]));
        assert!(contains(&argv, &["--tmpfs", &home_dir().to_string_lossy()]));
    }

    #[test]
    fn the_lean_project_stays_writable() {
        assert!(contains(
            &wrapped(),
            &[
                "--bind",
                "/srv/formal/lean_project",
                "/srv/formal/lean_project"
            ]
        ));
    }

    #[test]
    fn home_is_masked_before_the_lean_project_is_restored() {
        let paths = Paths::under(home_dir().join("formal"));
        let toolchain = Toolchain::new(PathBuf::from("/srv/elan"), &OsString::from("/usr/bin"));
        let argv = Sandbox::new(
            Mode::Auto,
            Some(PathBuf::from("/usr/bin/bwrap")),
            &paths,
            &toolchain,
        )
        .wrap(&CMD)
        .expect("bubblewrap is available")
        .argv;
        let masked = argv
            .iter()
            .position(|part| part == home_dir().as_os_str())
            .expect("the home tmpfs");
        let restored = argv
            .iter()
            .position(|part| part == paths.lean_project_dir.as_os_str())
            .expect("the project bind");
        assert!(masked < restored);
    }

    #[test]
    fn describe_names_the_reason_there_is_no_sandbox() {
        assert_eq!(
            sandbox(Mode::Off, Some("/usr/bin/bwrap")).describe(),
            "off (FORMAL_SANDBOX)"
        );
        assert_eq!(
            sandbox(Mode::Auto, None).describe(),
            "unavailable — install bubblewrap"
        );
        assert_eq!(
            sandbox(Mode::Auto, Some("/usr/bin/bwrap")).describe(),
            "bubblewrap"
        );
    }
}
