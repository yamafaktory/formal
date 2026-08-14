//! The Rust key held to the digests Python recorded.
//!
//! `tests/fixtures/cache_keys.json` is the port oracle: 148 keys from properties
//! formal produced while checking its own source, plus 17 crafted inputs for
//! rules the corpus does not reach. Everything else about the cache says the key
//! discriminates. This says what the key *is* — a port that gets the framing,
//! the operator table or the ordering subtly wrong passes every behavioural test
//! and silently invalidates every cached proof in existence.

use std::{
    collections::HashMap,
    fs,
    path::PathBuf,
};

use formal_core::proof_cache::cache_key;
use serde::Deserialize;

#[derive(Deserialize)]
struct Entry {
    name: Option<String>,
    inputs: [String; 3],
    key: String,
}

#[derive(Deserialize)]
struct Golden {
    corpus: Vec<Entry>,
    crafted: Vec<Entry>,
}

impl Entry {
    fn computed(&self) -> String {
        let [function_code, kind, formal] = &self.inputs;
        cache_key(function_code, kind, formal)
    }

    fn label(&self) -> String {
        self.name.clone().unwrap_or_else(|| self.inputs.join(" / "))
    }
}

fn golden() -> Golden {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/cache_keys.json");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{} — {e}", path.display()));
    serde_json::from_str(&text).expect("the golden file is the shape the recorder wrote")
}

fn moved(entries: &[Entry]) -> Vec<String> {
    entries
        .iter()
        .filter(|entry| entry.computed() != entry.key)
        .map(Entry::label)
        .collect()
}

#[test]
fn the_corpus_keys_have_not_moved() {
    assert_eq!(moved(&golden().corpus), Vec::<String>::new());
}

#[test]
fn the_crafted_keys_have_not_moved() {
    assert_eq!(moved(&golden().crafted), Vec::<String>::new());
}

#[test]
fn the_corpus_is_the_size_it_was_measured_at() {
    assert_eq!(golden().corpus.len(), 148);
}

#[test]
fn every_property_in_the_corpus_gets_its_own_key() {
    let golden = golden();
    let mut seen: HashMap<String, String> = HashMap::new();
    for entry in &golden.corpus {
        let key = entry.computed();
        if let Some(clash) = seen.get(&key) {
            panic!("{} collides with {clash}", entry.label());
        }
        seen.insert(key, entry.label());
    }
    assert_eq!(seen.len(), golden.corpus.len());
}

fn crafted() -> HashMap<String, String> {
    golden()
        .crafted
        .into_iter()
        .map(|entry| {
            (
                entry.name.clone().expect("a crafted entry is named"),
                entry.key,
            )
        })
        .collect()
}

#[test]
fn spelling_an_operator_either_way_gives_one_key() {
    let keys = crafted();
    assert_eq!(
        keys["ascii and unicode operators agree"],
        keys["the same statement written in symbols"]
    );
    assert_eq!(
        keys["iff is matched before the arrow inside it"],
        keys["iff written as a symbol"]
    );
}

#[test]
fn a_word_operator_is_not_matched_inside_an_identifier() {
    let keys = crafted();
    assert_ne!(
        keys["word operators only count on a boundary"],
        keys["letters that merely spell one do not"]
    );
}

#[test]
fn no_field_can_imitate_the_boundary_of_another() {
    let keys = crafted();
    assert_ne!(
        keys["fields cannot imitate each other's boundary"],
        keys["the other side of that boundary"]
    );
}

#[test]
fn indentation_survives_but_trailing_space_does_not() {
    let keys = crafted();
    assert_eq!(
        keys["indentation is significant in the code"],
        keys["but trailing whitespace in the code is not"]
    );
}
