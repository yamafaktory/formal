//! Locating the Lean toolchain without requiring it on the user's shell PATH.

use std::{
    collections::BTreeMap,
    env,
    ffi::OsString,
    os::unix::fs::PermissionsExt,
    path::{
        Path,
        PathBuf,
    },
};

use crate::{
    env::Env,
    paths::{
        expanduser,
        home_dir,
    },
};

/// Where elan keeps the Lean toolchains, and the PATH that finds them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Toolchain {
    /// The elan installation root.
    pub elan_home: PathBuf,
    /// The PATH to search, elan's `bin` first.
    pub search_path: OsString,
}

fn elan_home(env: &Env) -> PathBuf {
    env.get("ELAN_HOME")
        .map_or_else(|| home_dir().join(".elan"), expanduser)
}

/// Put elan's `bin` in front of `base`, unless it is absent or already there.
fn search_path(elan_home: &Path, base: &OsString) -> OsString {
    let bin_dir = elan_home.join("bin");
    let entries: Vec<PathBuf> = env::split_paths(base).collect();
    if !bin_dir.is_dir() || entries.iter().any(|entry| entry == &bin_dir) {
        return base.clone();
    }
    if base.is_empty() {
        return bin_dir.into_os_string();
    }
    env::join_paths(std::iter::once(bin_dir).chain(entries)).unwrap_or_else(|_| base.clone())
}

impl Toolchain {
    /// Resolve elan and the search path from the process environment, once.
    #[must_use]
    pub fn from_env() -> Self {
        Self::resolve(&Env::process())
    }

    /// The same, from configuration that was collected rather than read.
    #[must_use]
    pub fn resolve(config: &Env) -> Self {
        let elan_home = elan_home(config);
        let base = config
            .get("PATH")
            .map_or_else(OsString::new, OsString::from);
        Self {
            search_path: search_path(&elan_home, &base),
            elan_home,
        }
    }

    /// The same, for a stated elan root and a stated PATH.
    #[must_use]
    pub fn new(elan_home: PathBuf, base: &OsString) -> Self {
        Self {
            search_path: search_path(&elan_home, base),
            elan_home,
        }
    }

    /// Where elan's binaries are, whether or not that directory exists.
    #[must_use]
    pub fn bin_dir(&self) -> PathBuf {
        self.elan_home.join("bin")
    }

    /// The first executable named `name` on the search path.
    #[must_use]
    pub fn which(&self, name: &str) -> Option<PathBuf> {
        env::split_paths(&self.search_path)
            .map(|dir| dir.join(name))
            .find(|candidate| is_executable(candidate))
    }

    /// The process environment with the search path substituted in.
    #[must_use]
    pub fn env(&self) -> BTreeMap<OsString, OsString> {
        let mut merged: BTreeMap<OsString, OsString> = env::vars_os().collect();
        merged.insert(OsString::from("PATH"), self.search_path.clone());
        merged
    }
}

fn is_executable(path: &Path) -> bool {
    path.metadata()
        .is_ok_and(|meta| meta.is_file() && meta.permissions().mode() & 0o111 != 0)
}

#[cfg(test)]
mod tests {
    use std::fs;

    use tempfile::TempDir;

    use super::*;

    fn with_elan_bin() -> (TempDir, PathBuf) {
        let dir = TempDir::new().expect("a temporary directory");
        let bin = dir.path().join("bin");
        fs::create_dir(&bin).expect("the bin directory is creatable");
        (dir, bin)
    }

    fn toolchain(elan_home: &Path, base: &str) -> Toolchain {
        Toolchain::new(elan_home.to_path_buf(), &OsString::from(base))
    }

    #[test]
    fn elan_bin_goes_in_front() {
        let (dir, bin) = with_elan_bin();
        assert_eq!(
            toolchain(dir.path(), "/usr/bin").search_path,
            OsString::from(format!("{}:/usr/bin", bin.display()))
        );
    }

    #[test]
    fn an_entry_already_present_is_not_duplicated() {
        let (dir, bin) = with_elan_bin();
        let base = format!("/usr/bin:{}", bin.display());
        assert_eq!(
            toolchain(dir.path(), &base).search_path,
            OsString::from(&base)
        );
    }

    #[test]
    fn a_missing_elan_directory_leaves_the_path_untouched() {
        let dir = TempDir::new().expect("a temporary directory");
        assert_eq!(
            toolchain(&dir.path().join("absent"), "/usr/bin").search_path,
            OsString::from("/usr/bin")
        );
    }

    #[test]
    fn an_empty_base_yields_just_elan() {
        let (dir, bin) = with_elan_bin();
        assert_eq!(toolchain(dir.path(), "").search_path, bin.into_os_string());
    }

    #[test]
    fn a_binary_under_elan_is_found() {
        let (dir, bin) = with_elan_bin();
        let lake = bin.join("lake");
        fs::write(&lake, "#!/bin/sh\n").expect("the file is writable");
        fs::set_permissions(&lake, fs::Permissions::from_mode(0o755))
            .expect("the mode is settable");
        assert_eq!(
            toolchain(dir.path(), "/nonexistent").which("lake"),
            Some(lake)
        );
    }

    #[test]
    fn a_file_that_is_not_executable_is_not_a_binary() {
        let (dir, bin) = with_elan_bin();
        fs::write(bin.join("lake"), "#!/bin/sh\n").expect("the file is writable");
        assert_eq!(toolchain(dir.path(), "/nonexistent").which("lake"), None);
    }

    #[test]
    fn nothing_is_found_when_elan_is_absent() {
        let dir = TempDir::new().expect("a temporary directory");
        assert_eq!(
            toolchain(&dir.path().join("absent"), "/nonexistent").which("lake"),
            None
        );
    }

    #[test]
    fn the_environment_keeps_its_other_variables() {
        let (dir, _) = with_elan_bin();
        let env = toolchain(dir.path(), "/usr/bin").env();
        assert!(env.contains_key(&OsString::from("HOME")));
        assert_eq!(
            env[&OsString::from("PATH")],
            toolchain(dir.path(), "/usr/bin").search_path
        );
    }
}
