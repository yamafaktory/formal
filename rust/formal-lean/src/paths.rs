//! Where formal keeps its state, and where the Lean project lives.
//!
//! Python read these from the environment at import time and froze them in module
//! constants. Here they are resolved once into a value that is passed down, which
//! is the same freeze made visible — and the only way to let a test say what the
//! paths are, since mutating the environment of a running process is unsound once
//! more than one thread exists.

use std::{
    env,
    path::{
        Path,
        PathBuf,
    },
};

use crate::env::Env;

/// The checkout this binary was built from.
///
/// Python asked `__file__` where it was and walked up two directories. A compiled
/// binary has no such answer at runtime, so the question is settled at build time
/// and confirmed against the tree it names — an installed binary whose checkout is
/// gone falls through to the XDG location exactly as an installed wheel did.
const CHECKOUT_ROOT: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../..");

/// The filesystem locations formal reads and writes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Paths {
    /// The root everything else defaults to sitting under.
    pub formal_home: PathBuf,
    /// The Lake project Lean is invoked in.
    pub lean_project_dir: PathBuf,
    /// Where run results are written.
    pub results_dir: PathBuf,
    /// Where accepted proofs are cached.
    pub proof_cache_dir: PathBuf,
}

/// `Path.expanduser()`, which is what Python applied to every one of these.
pub(crate) fn expanduser(raw: &str) -> PathBuf {
    if let Some(home) = env::var_os("HOME").filter(|_| raw == "~" || raw.starts_with("~/")) {
        let home = PathBuf::from(home);
        return if raw == "~" {
            home
        } else {
            home.join(&raw[2..])
        };
    }
    PathBuf::from(raw)
}

/// The user's home directory, or the root when there is none to speak of.
pub(crate) fn home_dir() -> PathBuf {
    env::var_os("HOME").map_or_else(|| PathBuf::from("/"), PathBuf::from)
}

fn checkout_root() -> Option<PathBuf> {
    let candidate = Path::new(CHECKOUT_ROOT);
    if !candidate.join("lean_project/lakefile.toml").is_file() {
        return None;
    }
    // Python's Path.resolve() flattened the walk up out of the package directory,
    // and every one of these paths gets printed by `formal status`.
    Some(
        candidate
            .canonicalize()
            .unwrap_or_else(|_| candidate.to_path_buf()),
    )
}

fn default_home(env: &Env) -> PathBuf {
    if let Some(checkout) = checkout_root() {
        return checkout;
    }
    let xdg = env
        .get("XDG_DATA_HOME")
        .map_or_else(|| home_dir().join(".local/share"), PathBuf::from);
    xdg.join("formal")
}

impl Paths {
    /// Resolve every location from the process environment, once.
    #[must_use]
    pub fn from_env() -> Self {
        Self::resolve(&Env::process())
    }

    /// The same, from configuration that was collected rather than read.
    #[must_use]
    pub fn resolve(env: &Env) -> Self {
        let formal_home = env
            .get("FORMAL_HOME")
            .map_or_else(|| default_home(env), expanduser);
        let defaults = Self::under(formal_home);
        let results_dir = env
            .get("FORMAL_RESULTS_DIR")
            .map_or(defaults.results_dir, expanduser);
        Self {
            lean_project_dir: env
                .get("LEAN_PROJECT_DIR")
                .map_or(defaults.lean_project_dir, expanduser),
            proof_cache_dir: env
                .get("PROOF_CACHE_DIR")
                .map_or_else(|| results_dir.join("cache"), expanduser),
            results_dir,
            ..defaults
        }
    }

    /// The defaults for a given root, with nothing read from the environment.
    #[must_use]
    pub fn under(formal_home: PathBuf) -> Self {
        let results_dir = formal_home.join("results");
        Self {
            lean_project_dir: formal_home.join("lean_project"),
            proof_cache_dir: results_dir.join("cache"),
            results_dir,
            formal_home,
        }
    }

    /// Where scratch Lean files are written for a verification run.
    #[must_use]
    pub fn verify_dir(&self) -> PathBuf {
        self.lean_project_dir.join("Verify")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Env;

    #[test]
    fn every_location_hangs_off_the_home_it_was_given() {
        let paths = Paths::under(PathBuf::from("/srv/formal"));
        assert_eq!(
            paths.lean_project_dir,
            Path::new("/srv/formal/lean_project")
        );
        assert_eq!(
            paths.verify_dir(),
            Path::new("/srv/formal/lean_project/Verify")
        );
    }

    #[test]
    fn a_stated_home_is_where_everything_hangs_off() {
        let paths = Paths::resolve(&Env::from_pairs([("FORMAL_HOME", "/srv/formal")]));
        assert_eq!(paths.formal_home, Path::new("/srv/formal"));
        assert_eq!(
            paths.proof_cache_dir,
            Path::new("/srv/formal/results/cache")
        );
    }

    #[test]
    fn each_location_can_be_moved_on_its_own() {
        let paths = Paths::resolve(&Env::from_pairs([
            ("FORMAL_HOME", "/srv/formal"),
            ("LEAN_PROJECT_DIR", "/elsewhere/lean"),
            ("PROOF_CACHE_DIR", "/elsewhere/cache"),
        ]));
        assert_eq!(paths.lean_project_dir, Path::new("/elsewhere/lean"));
        assert_eq!(paths.proof_cache_dir, Path::new("/elsewhere/cache"));
        assert_eq!(
            paths.results_dir,
            Path::new("/srv/formal/results"),
            "which was not moved"
        );
    }

    #[test]
    fn a_results_directory_takes_the_cache_with_it() {
        let paths = Paths::resolve(&Env::from_pairs([
            ("FORMAL_HOME", "/srv/formal"),
            ("FORMAL_RESULTS_DIR", "/elsewhere/results"),
        ]));
        assert_eq!(paths.proof_cache_dir, Path::new("/elsewhere/results/cache"));
    }

    #[test]
    fn a_blank_setting_is_not_a_location() {
        let paths = Paths::resolve(&Env::from_pairs([
            ("FORMAL_HOME", "/srv/formal"),
            ("LEAN_PROJECT_DIR", "  "),
        ]));
        assert_eq!(
            paths.lean_project_dir,
            Path::new("/srv/formal/lean_project")
        );
    }

    #[test]
    fn the_checkout_is_found_when_this_is_built_from_one() {
        assert_eq!(
            checkout_root().is_some(),
            Path::new(CHECKOUT_ROOT).join("lean_project").is_dir()
        );
    }
}
