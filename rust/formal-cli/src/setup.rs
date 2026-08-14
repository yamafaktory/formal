//! Installation of the Lean toolchain, driven by `formal setup`.

use std::{
    fs,
    io::{
        BufRead,
        Write,
    },
    path::Path,
    process::{
        Command,
        Stdio,
    },
    time::Duration,
};

use formal_lean::{
    paths::Paths,
    sandbox::Sandbox,
    toolchain::Toolchain,
};

use crate::status::mathlib_lib;

/// Where elan's own installer lives.
const ELAN_INSTALLER: &str =
    "https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh";

/// Where to send someone who would rather not run a script off the internet.
const LEAN_INSTALL_DOCS: &str = "https://lean-lang.org/install/";

/// How long the installer download gets.
const DOWNLOAD_TIMEOUT: Duration = Duration::from_mins(2);

/// The Lean project formal ships, for when it is not running from a checkout.
const TEMPLATE: &[(&str, &str)] = &[
    (
        "lakefile.toml",
        include_str!("../../../lean_project/lakefile.toml"),
    ),
    (
        "lean-toolchain",
        include_str!("../../../lean_project/lean-toolchain"),
    ),
    (
        "lake-manifest.json",
        include_str!("../../../lean_project/lake-manifest.json"),
    ),
    (
        "Warmup.lean",
        include_str!("../../../lean_project/Warmup.lean"),
    ),
];

/// Asking, and being answered.
///
/// A trait so the install path can be tested without a terminal — Python's tests
/// patched `input`, which is the same seam said out loud.
pub(crate) trait Prompt {
    /// Tell the person what is about to happen.
    fn say(&self, message: &str);

    /// Ask a yes-or-no question that defaults to yes.
    fn confirm(&self, question: &str) -> bool;
}

/// A real terminal.
#[derive(Debug, Default)]
pub(crate) struct Console;

impl Prompt for Console {
    fn say(&self, message: &str) {
        println!("{message}");
    }

    fn confirm(&self, question: &str) -> bool {
        print!("{question}");
        let _ = std::io::stdout().flush();
        let mut answer = String::new();
        // End of input is not a no: a non-interactive run should proceed on the
        // default rather than stop on a question nobody can see.
        if std::io::stdin().lock().read_line(&mut answer).unwrap_or(0) == 0 {
            return true;
        }
        !answer.trim().to_lowercase().starts_with('n')
    }
}

/// Whether `listing` names `version` among the toolchains elan has.
///
/// Compared on the first field: elan marks the default with a trailing `(default)`
/// and a substring test would match a version that merely starts the same way.
#[must_use]
pub(crate) fn names_the_version(listing: &str, version: &str) -> bool {
    listing
        .lines()
        .filter(|line| !line.trim().is_empty())
        .filter_map(|line| line.split_whitespace().next())
        .any(|first| first == version)
}

/// The Lean version the project pins, if it says.
#[must_use]
pub(crate) fn lean_version(paths: &Paths) -> Option<String> {
    fs::read_to_string(paths.lean_project_dir.join("lean-toolchain"))
        .ok()
        .map(|text| text.trim().to_string())
        .filter(|version| !version.is_empty())
}

/// Copy the bundled Lean project into place when running outside a checkout.
pub(crate) fn materialize_lean_project(paths: &Paths, prompt: &dyn Prompt) -> bool {
    let project = &paths.lean_project_dir;
    if project.join("lakefile.toml").is_file() {
        return true;
    }

    prompt.say(&format!(
        "Creating the Lean project in {}...",
        project.display()
    ));
    if fs::create_dir_all(project.join("Verify")).is_err() {
        prompt.say(&format!("Could not create {}.", project.display()));
        return false;
    }
    for (name, contents) in TEMPLATE {
        if fs::write(project.join(name), contents).is_err() {
            prompt.say(&format!("Could not write {name}."));
            return false;
        }
    }
    project.join("lakefile.toml").is_file()
}

fn run(program: &Path, args: &[&str], toolchain: &Toolchain, cwd: Option<&Path>) -> bool {
    let mut command = Command::new(program);
    command.args(args).env_clear().envs(toolchain.env());
    if let Some(cwd) = cwd {
        command.current_dir(cwd);
    }
    command.status().is_ok_and(|status| status.success())
}

fn lake(paths: &Paths, toolchain: &Toolchain, args: &[&str]) -> bool {
    toolchain
        .which("lake")
        .is_some_and(|lake| run(&lake, args, toolchain, Some(&paths.lean_project_dir)))
}

/// Download elan's installer and run it, having asked first.
pub(crate) fn install_elan(toolchain: &Toolchain, prompt: &dyn Prompt) -> bool {
    prompt.say("elan (the Lean toolchain manager) is not installed.");
    prompt.say(&format!(
        "If your package manager provides it, prefer that — see {LEAN_INSTALL_DOCS}"
    ));
    prompt.say("Any elan already on your system is used as-is, however it was installed.");
    prompt.say("");
    if !prompt.confirm(&format!(
        "Otherwise, run elan's official installer into {}? [Y/n]: ",
        toolchain.elan_home.display()
    )) {
        prompt.say("Skipped — install elan, then re-run.");
        return false;
    }

    let script = match download(ELAN_INSTALLER) {
        Ok(script) => script,
        Err(e) => {
            prompt.say(&format!("Could not download the elan installer: {e}"));
            return false;
        }
    };
    match pipe_to_shell(&script, &["-s", "--", "-y", "--default-toolchain", "none"]) {
        Ok(true) => true,
        Ok(false) => {
            prompt.say("elan installation failed.");
            false
        }
        Err(e) => {
            prompt.say(&format!("elan installation failed: {e}"));
            false
        }
    }
}

fn download(url: &str) -> std::io::Result<String> {
    let output = Command::new("curl")
        .args([
            "-sSf",
            "--max-time",
            &DOWNLOAD_TIMEOUT.as_secs().to_string(),
            url,
        ])
        .output()?;
    if !output.status.success() {
        return Err(std::io::Error::other(
            String::from_utf8_lossy(&output.stderr).trim().to_string(),
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

fn pipe_to_shell(script: &str, args: &[&str]) -> std::io::Result<bool> {
    let mut child = Command::new("sh")
        .args(args)
        .stdin(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .take()
        .ok_or_else(|| std::io::Error::other("no stdin to write the script to"))?
        .write_all(script.as_bytes())?;
    Ok(child.wait()?.success())
}

/// Make sure something can drive Lean, installing elan if asked to.
pub(crate) fn ensure_elan(toolchain: &Toolchain, prompt: &dyn Prompt) -> bool {
    if toolchain.which("lake").is_some() || toolchain.which("elan").is_some() {
        return true;
    }
    install_elan(toolchain, prompt)
}

/// Whether elan already has the version the project pins.
#[must_use]
pub(crate) fn toolchain_installed(elan: &Path, version: &str, toolchain: &Toolchain) -> bool {
    Command::new(elan)
        .args(["toolchain", "list"])
        .env_clear()
        .envs(toolchain.env())
        .output()
        .is_ok_and(|output| {
            output.status.success()
                && names_the_version(&String::from_utf8_lossy(&output.stdout), version)
        })
}

/// Install the pinned Lean, unless elan is absent and lake is already there.
pub(crate) fn ensure_toolchain(paths: &Paths, toolchain: &Toolchain, prompt: &dyn Prompt) -> bool {
    let Some(elan) = toolchain.which("elan") else {
        return toolchain.which("lake").is_some();
    };

    let Some(version) = lean_version(paths) else {
        prompt.say(&format!(
            "Missing {} — cannot tell which Lean version to install.",
            paths.lean_project_dir.join("lean-toolchain").display()
        ));
        return false;
    };

    if toolchain_installed(&elan, &version, toolchain) {
        return true;
    }

    prompt.say(&format!(
        "Installing Lean {version} via elan (a few hundred MB)..."
    ));
    if !run(&elan, &["toolchain", "install", &version], toolchain, None) {
        return false;
    }
    toolchain.which("lake").is_some()
}

/// Get from nothing to a Lean that can check a proof.
pub(crate) fn install_lean(paths: &Paths, toolchain: &Toolchain, prompt: &dyn Prompt) -> bool {
    if !materialize_lean_project(paths, prompt) {
        return false;
    }
    if !ensure_elan(toolchain, prompt) || !ensure_toolchain(paths, toolchain, prompt) {
        return false;
    }

    if mathlib_lib(paths).is_dir() {
        prompt.say("Mathlib already built — skipping.");
        return true;
    }

    prompt.say("Fetching Mathlib.");
    prompt.say("This downloads several GB of prebuilt oleans and takes a few minutes.");
    if !prompt.confirm("Continue? [Y/n]: ") {
        prompt.say("Skipped — no proofs can run until this completes.");
        return false;
    }

    let mut steps: Vec<(&str, Vec<&str>)> = Vec::new();
    if paths.lean_project_dir.join("lake-manifest.json").is_file() {
        prompt.say("  Using the dependency revisions pinned in lake-manifest.json.");
    } else {
        steps.push(("Resolving dependencies", vec!["update"]));
    }
    steps.push((
        "Fetching prebuilt Mathlib oleans",
        vec!["exe", "cache", "get"],
    ));
    steps.push(("Precompiling the warmup module", vec!["build", "Warmup"]));

    for (description, args) in steps {
        prompt.say(&format!("  {description}..."));
        if !lake(paths, toolchain, &args) {
            prompt.say(&format!("  Failed: lake {}", args.join(" ")));
            return false;
        }
    }
    true
}

/// `formal setup`, reporting whether the installation is now usable.
pub(crate) fn install(
    paths: &Paths,
    toolchain: &Toolchain,
    sandbox: &Sandbox,
    prompt: &dyn Prompt,
) -> bool {
    if !install_lean(paths, toolchain, prompt) {
        return false;
    }

    if sandbox.describe().starts_with("unavailable") {
        prompt.say("");
        prompt.say("bubblewrap is not installed — Lean proofs will run unsandboxed.");
        prompt.say("  Arch: pacman -S bubblewrap    Debian: apt install bubblewrap");
    }

    prompt.say("");
    prompt.say("Check the installation with:  formal status");
    true
}

#[cfg(test)]
mod tests {
    use std::{
        cell::RefCell,
        path::PathBuf,
    };

    use tempfile::TempDir;

    use super::*;

    /// Answers as told, and remembers what it was asked.
    #[derive(Default)]
    struct Scripted {
        answer: bool,
        said: RefCell<Vec<String>>,
        asked: RefCell<Vec<String>>,
    }

    impl Scripted {
        fn refusing() -> Self {
            Self::default()
        }

        fn transcript(&self) -> String {
            self.said.borrow().join("\n")
        }
    }

    impl Prompt for Scripted {
        fn say(&self, message: &str) {
            self.said.borrow_mut().push(message.to_string());
        }

        fn confirm(&self, question: &str) -> bool {
            self.asked.borrow_mut().push(question.to_string());
            self.answer
        }
    }

    mod the_pinned_version {
        use super::*;

        #[test]
        fn a_listing_that_names_it_counts() {
            let listing = "leanprover/lean4:v4.29.0\nstable (default)\n";
            assert!(names_the_version(listing, "leanprover/lean4:v4.29.0"));
        }

        #[test]
        fn the_default_marker_does_not_get_in_the_way() {
            let listing = "leanprover/lean4:v4.29.0 (default)\n";
            assert!(names_the_version(listing, "leanprover/lean4:v4.29.0"));
        }

        #[test]
        fn a_version_that_merely_starts_the_same_does_not_count() {
            let listing = "leanprover/lean4:v4.29.0-rc1\n";
            assert!(!names_the_version(listing, "leanprover/lean4:v4.29.0"));
        }

        #[test]
        fn nothing_installed_names_nothing() {
            assert!(!names_the_version("", "leanprover/lean4:v4.29.0"));
            assert!(!names_the_version("\n  \n", "leanprover/lean4:v4.29.0"));
        }

        #[test]
        fn a_project_that_pins_nothing_has_no_version() {
            let dir = TempDir::new().expect("a temporary directory");
            assert_eq!(lean_version(&Paths::under(dir.path().to_path_buf())), None);
        }

        #[test]
        fn a_pin_is_read_without_its_newline() {
            let dir = TempDir::new().expect("a temporary directory");
            let paths = Paths::under(dir.path().to_path_buf());
            fs::create_dir_all(&paths.lean_project_dir).expect("writable");
            fs::write(
                paths.lean_project_dir.join("lean-toolchain"),
                "leanprover/lean4:v4.29.0\n",
            )
            .expect("writable");
            assert_eq!(
                lean_version(&paths).as_deref(),
                Some("leanprover/lean4:v4.29.0")
            );
        }
    }

    mod materialising {
        use super::*;

        #[test]
        fn the_bundled_project_is_written_out() {
            let dir = TempDir::new().expect("a temporary directory");
            let paths = Paths::under(dir.path().to_path_buf());
            let prompt = Scripted::refusing();

            assert!(materialize_lean_project(&paths, &prompt));
            for (name, _) in TEMPLATE {
                assert!(paths.lean_project_dir.join(name).is_file(), "{name}");
            }
            assert!(
                paths.verify_dir().is_dir(),
                "and somewhere to write scratch files"
            );
            assert!(prompt.transcript().contains("Creating the Lean project"));
        }

        #[test]
        fn the_bundled_pin_is_the_one_the_checkout_uses() {
            let dir = TempDir::new().expect("a temporary directory");
            let paths = Paths::under(dir.path().to_path_buf());
            materialize_lean_project(&paths, &Scripted::refusing());
            assert_eq!(lean_version(&paths), lean_version(&Paths::from_env()));
        }

        #[test]
        fn an_existing_project_is_left_exactly_as_it_is() {
            let dir = TempDir::new().expect("a temporary directory");
            let paths = Paths::under(dir.path().to_path_buf());
            fs::create_dir_all(&paths.lean_project_dir).expect("writable");
            fs::write(paths.lean_project_dir.join("lakefile.toml"), "mine").expect("writable");

            let prompt = Scripted::refusing();
            assert!(materialize_lean_project(&paths, &prompt));
            assert_eq!(
                fs::read_to_string(paths.lean_project_dir.join("lakefile.toml")).expect("readable"),
                "mine"
            );
            assert_eq!(prompt.transcript(), "", "and nothing was said about it");
        }

        #[test]
        fn a_place_that_cannot_be_written_is_reported_rather_than_assumed() {
            let dir = TempDir::new().expect("a temporary directory");
            let blocked = dir.path().join("blocked");
            fs::write(&blocked, "not a directory").expect("writable");
            let paths = Paths::under(blocked);
            let prompt = Scripted::refusing();
            assert!(!materialize_lean_project(&paths, &prompt));
            assert!(
                prompt.transcript().contains("Could not create"),
                "{}",
                prompt.transcript()
            );
        }
    }

    mod asking_first {
        use super::*;

        fn nowhere() -> Toolchain {
            Toolchain::new(
                PathBuf::from("/nonexistent/elan"),
                &std::ffi::OsString::from("/nonexistent"),
            )
        }

        #[test]
        fn a_refusal_installs_nothing() {
            let prompt = Scripted::refusing();
            assert!(!install_elan(&nowhere(), &prompt));
            assert!(
                prompt.transcript().contains("Skipped — install elan"),
                "{}",
                prompt.transcript()
            );
        }

        #[test]
        fn the_package_manager_is_recommended_before_the_script() {
            let prompt = Scripted::refusing();
            install_elan(&nowhere(), &prompt);
            let transcript = prompt.transcript();
            assert!(transcript.contains(LEAN_INSTALL_DOCS), "{transcript}");
            assert!(
                transcript
                    .find("package manager")
                    .is_some_and(|manager| transcript
                        .find("official installer")
                        .is_none_or(|script| manager < script)),
                "{transcript}"
            );
        }

        #[test]
        fn the_question_names_where_it_would_install() {
            let prompt = Scripted::refusing();
            install_elan(&nowhere(), &prompt);
            assert!(
                prompt.asked.borrow()[0].contains("/nonexistent/elan"),
                "{:?}",
                prompt.asked.borrow()
            );
        }

        #[test]
        fn a_missing_pin_stops_the_toolchain_install() {
            let dir = TempDir::new().expect("a temporary directory");
            let prompt = Scripted::refusing();
            let paths = Paths::under(dir.path().to_path_buf());
            assert!(
                !ensure_toolchain(&paths, &nowhere(), &prompt) || nowhere().which("lake").is_some()
            );
        }

        #[test]
        fn nothing_at_all_installed_means_nothing_can_be_ensured() {
            let prompt = Scripted::refusing();
            assert!(!ensure_elan(&nowhere(), &prompt));
        }
    }
}
