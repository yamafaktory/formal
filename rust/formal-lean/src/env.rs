//! Where configuration comes from.
//!
//! Python read the environment at the point of use and had the CLI fill it in
//! first, with `os.environ.setdefault` over a `.env` file. Setting a variable in a
//! live process is unsound in Rust 2024, and rightly — the server is threaded — so
//! the answers are collected once into a value that is passed down instead.
//!
//! The precedence is what `setdefault` gave: a variable already in the
//! environment wins, and `.env` fills the gaps.

use std::{
    collections::BTreeMap,
    fs,
    path::Path,
};

/// The configuration this process was started with.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Env {
    values: BTreeMap<String, String>,
}

impl Env {
    /// Just the process environment.
    #[must_use]
    pub fn process() -> Self {
        Self {
            values: std::env::vars().collect(),
        }
    }

    /// The process environment, with `.env` filling in what it does not set.
    ///
    /// A `.env` that is not there, or not readable, is not an error: it is
    /// optional by design.
    #[must_use]
    pub fn with_dotenv(path: &Path) -> Self {
        let mut env = Self::process();
        for (key, value) in parse_dotenv(&fs::read_to_string(path).unwrap_or_default()) {
            env.values.entry(key).or_insert(value);
        }
        env
    }

    /// Configuration stated outright, for a test that should not depend on the
    /// machine it runs on.
    #[must_use]
    pub fn from_pairs<K: Into<String>, V: Into<String>>(
        pairs: impl IntoIterator<Item = (K, V)>,
    ) -> Self {
        Self {
            values: pairs
                .into_iter()
                .map(|(k, v)| (k.into(), v.into()))
                .collect(),
        }
    }

    /// One setting, absent when unset or blank.
    ///
    /// Blank counts as absent because every caller trimmed and tested for empty
    /// anyway, and `FORMAL_HOST=` should mean "I did not choose", not "the empty
    /// host".
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&str> {
        self.values
            .get(key)
            .map(|value| value.trim())
            .filter(|value| !value.is_empty())
    }

    /// One setting read as a number, absent when unset or unreadable.
    #[must_use]
    pub fn number<T: std::str::FromStr>(&self, key: &str) -> Option<T> {
        self.get(key).and_then(|value| value.parse().ok())
    }

    /// Every key this env knows about.
    #[must_use]
    pub fn keys(&self) -> Vec<&str> {
        self.values.keys().map(String::as_str).collect()
    }
}

/// The keys a `.env` file sets, in the order they appear.
///
/// A line without an `=` is not a setting, and a `#` line is a comment. Quotes
/// around a value are stripped, because a shell would have.
#[must_use]
pub fn parse_dotenv(text: &str) -> Vec<(String, String)> {
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .filter_map(|line| line.split_once('='))
        .map(|(key, value)| {
            (
                key.trim().to_string(),
                value.trim().trim_matches(['\'', '"']).to_string(),
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_blank_setting_is_no_setting() {
        let env = Env::from_pairs([("FORMAL_HOST", "  ")]);
        assert_eq!(env.get("FORMAL_HOST"), None);
    }

    #[test]
    fn a_setting_is_trimmed() {
        assert_eq!(
            Env::from_pairs([("FORMAL_HOST", " here ")]).get("FORMAL_HOST"),
            Some("here")
        );
    }

    #[test]
    fn a_number_that_is_not_one_is_no_setting() {
        let env = Env::from_pairs([("FORMAL_PORT", "eight")]);
        assert_eq!(env.number::<u16>("FORMAL_PORT"), None);
        assert_eq!(
            Env::from_pairs([("FORMAL_PORT", "1337")]).number::<u16>("FORMAL_PORT"),
            Some(1337)
        );
    }

    #[test]
    fn comments_and_lines_without_an_equals_are_not_settings() {
        let parsed = parse_dotenv("# a comment\nFORMAL_PORT=1337\nnot a setting\n\n");
        assert_eq!(parsed, [("FORMAL_PORT".to_string(), "1337".to_string())]);
    }

    #[test]
    fn quotes_around_a_value_come_off() {
        let parsed = parse_dotenv("A='one'\nB=\"two\"\nC=three");
        let values: Vec<&str> = parsed.iter().map(|(_, value)| value.as_str()).collect();
        assert_eq!(values, ["one", "two", "three"]);
    }

    #[test]
    fn a_value_containing_an_equals_keeps_it() {
        assert_eq!(
            parse_dotenv("A=b=c"),
            [("A".to_string(), "b=c".to_string())]
        );
    }

    #[test]
    fn the_environment_wins_over_the_file() {
        let dir = tempfile::TempDir::new().expect("a temporary directory");
        let path = dir.path().join(".env");
        fs::write(&path, "HOME=/nowhere\nFORMAL_MADE_UP=from the file\n").expect("writable");
        let env = Env::with_dotenv(&path);
        assert_ne!(
            env.get("HOME"),
            Some("/nowhere"),
            "the process already said what HOME is"
        );
        assert_eq!(env.get("FORMAL_MADE_UP"), Some("from the file"));
    }

    #[test]
    fn a_missing_file_is_not_an_error() {
        let dir = tempfile::TempDir::new().expect("a temporary directory");
        let env = Env::with_dotenv(&dir.path().join("absent"));
        assert_eq!(env.get("FORMAL_MADE_UP"), None);
    }
}
