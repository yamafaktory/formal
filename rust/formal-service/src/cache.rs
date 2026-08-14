//! Disk-backed cache for verified Lean theorem results.
//!
//! Only successful results are kept — a failure is always retried. Nothing here
//! may change a verdict: a write that cannot happen is a proof that costs a Lean
//! run next time, and that is all.
//!
//! What identifies an entry lives in `formal_core::proof_cache`, and is frozen by
//! a fixture. This is only where the bytes go.

use std::{
    fs,
    path::{
        Path,
        PathBuf,
    },
    time::{
        Duration,
        SystemTime,
    },
};

use formal_core::property::PropertyResult;
use formal_lean::{
    logger::{
        Tag,
        log,
    },
    paths::Paths,
};

/// How long an entry survives without being rewritten.
const DEFAULT_TTL: Duration = Duration::from_hours(24 * 7);

/// Where accepted proofs are kept, and for how long.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProofCache {
    dir: PathBuf,
    ttl: Duration,
}

impl ProofCache {
    /// A cache in a stated directory with a stated lifetime.
    #[must_use]
    pub fn new(dir: PathBuf, ttl: Duration) -> Self {
        Self { dir, ttl }
    }

    /// The cache this process would use, `PROOF_CACHE_TTL_DAYS` included.
    #[must_use]
    pub fn from_env(paths: &Paths) -> Self {
        let ttl = std::env::var("PROOF_CACHE_TTL_DAYS")
            .ok()
            .and_then(|value| value.trim().parse::<u64>().ok())
            .map_or(DEFAULT_TTL, |days| Duration::from_hours(days * 24));
        Self::new(paths.proof_cache_dir.clone(), ttl)
    }

    /// Where the entry for `key` would be.
    #[must_use]
    pub fn path(&self, key: &str) -> PathBuf {
        self.dir.join(format!("{key}.json"))
    }

    /// What was proved under `key`, if anything still is.
    ///
    /// An entry that will not parse is not an entry. It is left on disk to be
    /// overwritten or evicted rather than deleted here, because a read has no
    /// business changing what is stored.
    #[must_use]
    pub fn load(&self, key: &str) -> Option<PropertyResult> {
        let text = fs::read_to_string(self.path(key)).ok()?;
        serde_json::from_str(&text).ok()
    }

    /// Record what Lean accepted, or carry on if that is not possible.
    ///
    /// The cache is an optimisation and never changes a verdict, so every failure
    /// here is reported and swallowed.
    pub fn save(&self, key: &str, result: &PropertyResult) {
        if let Err(e) = self.try_save(key, result) {
            log(
                Tag::Cache,
                &format!("could not write {}… — {e}", short(key)),
            );
        }
    }

    fn try_save(&self, key: &str, result: &PropertyResult) -> std::io::Result<()> {
        fs::create_dir_all(&self.dir)?;
        let text = serde_json::to_string_pretty(result).map_err(std::io::Error::other)?;
        fs::write(self.path(key), text)?;
        self.evict_expired();
        Ok(())
    }

    /// Delete entries older than the lifetime.
    ///
    /// Runs after a successful write, so the entry just made always survives it.
    pub fn evict_expired(&self) {
        let Ok(entries) = fs::read_dir(&self.dir) else {
            return;
        };
        let Some(cutoff) = SystemTime::now().checked_sub(self.ttl) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().is_none_or(|extension| extension != "json") {
                continue;
            }
            if entry
                .metadata()
                .and_then(|meta| meta.modified())
                .is_ok_and(|at| at < cutoff)
            {
                let _ = fs::remove_file(&path);
            }
        }
    }
}

/// As much of a key as is worth putting in a log line.
fn short(key: &str) -> &str {
    let end = key
        .char_indices()
        .nth(12)
        .map_or(key.len(), |(index, _)| index);
    &key[..end]
}

/// Whether `dir` is a directory something could be written into.
#[must_use]
pub fn is_writable(dir: &Path) -> bool {
    dir.is_dir() && !fs::metadata(dir).is_ok_and(|meta| meta.permissions().readonly())
}

#[cfg(test)]
mod tests {
    use std::fs::File;

    use tempfile::TempDir;

    use super::*;

    fn result(property_id: &str) -> PropertyResult {
        PropertyResult {
            property_id: property_id.to_string(),
            description: "the result is never empty".to_string(),
            kind: "bound".to_string(),
            function: "f".to_string(),
            verified: true,
            lean_code: "theorem t : True := trivial".to_string(),
            lean_output: String::new(),
            retries: 0,
            status: "verified".to_string(),
            fidelity: "unchecked".to_string(),
            ..PropertyResult::default()
        }
    }

    fn cache(dir: &TempDir) -> ProofCache {
        ProofCache::new(dir.path().join("cache"), DEFAULT_TTL)
    }

    fn age(path: &Path, days: u64) {
        let stamp = SystemTime::now() - Duration::from_hours(days * 24);
        File::options()
            .write(true)
            .open(path)
            .expect("the entry opens")
            .set_modified(stamp)
            .expect("the timestamp is settable");
    }

    #[test]
    fn what_was_saved_comes_back() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        cache.save("abc", &result("p1"));
        let loaded = cache.load("abc").expect("the entry is there");
        assert_eq!(loaded.property_id, "p1");
        assert!(loaded.verified);
    }

    #[test]
    fn a_key_nobody_saved_is_nothing() {
        let dir = TempDir::new().expect("a temporary directory");
        assert_eq!(cache(&dir).load("nonexistent"), None);
    }

    #[test]
    fn an_entry_that_will_not_parse_is_nothing() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        fs::create_dir_all(&cache.dir).expect("the directory is creatable");
        fs::write(cache.path("bad"), "not valid json{{{").expect("the file is writable");
        assert_eq!(cache.load("bad"), None);
    }

    #[test]
    fn a_loaded_entry_is_not_yet_marked_as_cached() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        cache.save("abc", &result("p1"));
        assert!(
            !cache.load("abc").expect("the entry is there").cached,
            "the caller marks it, so that a saved result and a served one differ"
        );
    }

    #[test]
    fn the_modelling_survives_the_round_trip() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        cache.save(
            "abc",
            &PropertyResult {
                preconditions: vec!["n > 0".to_string()],
                assumptions: vec!["floats as rationals".to_string()],
                ..result("p1")
            },
        );
        let loaded = cache.load("abc").expect("the entry is there");
        assert_eq!(loaded.preconditions, ["n > 0"]);
        assert_eq!(loaded.assumptions, ["floats as rationals"]);
    }

    #[test]
    fn an_entry_past_its_lifetime_is_evicted_by_the_next_write() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        cache.save("old", &result("p1"));
        age(&cache.path("old"), 8);
        cache.save("new", &result("p2"));
        assert!(!cache.path("old").exists());
        assert!(cache.path("new").exists());
    }

    #[test]
    fn a_longer_lifetime_keeps_the_same_entry() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = ProofCache::new(dir.path().join("cache"), Duration::from_hours(365 * 24));
        cache.save("old", &result("p1"));
        age(&cache.path("old"), 8);
        cache.save("new", &result("p2"));
        assert!(cache.path("old").exists());
    }

    #[test]
    fn rewriting_an_entry_renews_it() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        cache.save("abc", &result("p1"));
        age(&cache.path("abc"), 8);
        cache.save("abc", &result("p1"));
        assert!(
            cache.path("abc").exists(),
            "the write happens before the eviction"
        );
    }

    #[test]
    fn nothing_else_in_the_directory_is_evicted() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        cache.save("abc", &result("p1"));
        let bystander = cache.dir.join("notes.txt");
        fs::write(&bystander, "keep me").expect("the file is writable");
        age(&bystander, 400);
        cache.save("def", &result("p2"));
        assert!(bystander.exists());
    }

    #[test]
    fn a_directory_that_cannot_be_written_is_not_an_error_anyone_sees() {
        let dir = TempDir::new().expect("a temporary directory");
        let locked = dir.path().join("locked");
        fs::create_dir(&locked).expect("the directory is creatable");
        let mut permissions = fs::metadata(&locked).expect("it exists").permissions();
        permissions.set_readonly(true);
        fs::set_permissions(&locked, permissions).expect("the mode is settable");

        ProofCache::new(locked.join("cache"), DEFAULT_TTL).save("abc", &result("p1"));
    }

    #[test]
    fn an_entry_that_cannot_be_overwritten_is_not_an_error_anyone_sees() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        fs::create_dir_all(&cache.dir).expect("the directory is creatable");
        fs::create_dir(cache.path("abc")).expect("something is in the way");

        cache.save("abc", &result("p1"));
        assert_eq!(cache.load("abc"), None);
    }

    #[test]
    fn a_short_key_is_not_cut_mid_character() {
        assert_eq!(short("abc"), "abc");
        assert_eq!(short("0123456789abcdef"), "0123456789ab");
    }
}
