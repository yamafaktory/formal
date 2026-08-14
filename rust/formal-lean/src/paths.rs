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

/// A trimmed environment variable, absent when unset or blank.
fn var(name: &str) -> Option<String> {
    env::var(name)
        .ok()
        .map(|value| value.trim().to_string())
        .filter(|value| !value.is_empty())
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
    candidate
        .join("lean_project/lakefile.toml")
        .is_file()
        .then(|| candidate.to_path_buf())
}

fn default_home() -> PathBuf {
    if let Some(checkout) = checkout_root() {
        return checkout;
    }
    let xdg = var("XDG_DATA_HOME").map_or_else(|| home_dir().join(".local/share"), PathBuf::from);
    xdg.join("formal")
}

impl Paths {
    /// Resolve every location from the environment, once.
    #[must_use]
    pub fn from_env() -> Self {
        let formal_home = var("FORMAL_HOME").map_or_else(default_home, |value| expanduser(&value));
        let defaults = Self::under(formal_home);
        let results_dir =
            var("FORMAL_RESULTS_DIR").map_or(defaults.results_dir, |v| expanduser(&v));
        Self {
            lean_project_dir: var("LEAN_PROJECT_DIR")
                .map_or(defaults.lean_project_dir, |v| expanduser(&v)),
            proof_cache_dir: var("PROOF_CACHE_DIR")
                .map_or_else(|| results_dir.join("cache"), |v| expanduser(&v)),
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
    fn the_checkout_is_found_when_this_is_built_from_one() {
        assert_eq!(
            checkout_root().is_some(),
            Path::new(CHECKOUT_ROOT).join("lean_project").is_dir()
        );
    }
}
