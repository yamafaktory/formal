//! The guide held to the digests the conformance suite recorded.
//!
//! `tests/conformance/golden/responses.json` pins every response over 400
//! characters as a SHA-256 and a character count, so the three topic bodies are
//! already frozen there — 32KB of prose that has to come back byte for byte
//! through the placeholder substitution, the kinds table, and every join between
//! the pieces. Getting one separator wrong moves the digest and nothing else.

use std::{
    fs,
    path::PathBuf,
};

use formal_core::guide;
use serde_json::Value;
use sha2::{
    Digest,
    Sha256,
};

/// The length above which the suite records a digest instead of the text.
const DIGEST_OVER: usize = 400;

fn golden() -> Value {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/conformance/golden/responses.json");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{} — {e}", path.display()));
    serde_json::from_str(&text).expect("the golden file is JSON")
}

/// The suite's own rule, applied to one value.
fn recorded(value: &Value) -> Value {
    match value {
        Value::String(text) if text.chars().count() > DIGEST_OVER => serde_json::json!({
            "sha256": format!("{:x}", Sha256::digest(text.as_bytes())),
            "chars": text.chars().count(),
        }),
        Value::String(_) | Value::Null | Value::Bool(_) | Value::Number(_) => value.clone(),
        Value::Array(items) => Value::Array(items.iter().map(recorded).collect()),
        Value::Object(fields) => Value::Object(
            fields
                .iter()
                .map(|(name, field)| (name.clone(), recorded(field)))
                .collect(),
        ),
    }
}

#[test]
fn every_topic_body_still_hashes_to_what_was_recorded() {
    let golden = golden();
    for name in guide::topic_names() {
        let served = guide::topic(name).unwrap_or_else(|| panic!("{name} is servable"));
        let expected = &golden[format!("guide_{name}")]["body"]["instructions"];
        assert_eq!(
            recorded(&Value::String(served)),
            *expected,
            "the {name} guidance no longer matches what the suite recorded"
        );
    }
}

#[test]
fn the_index_is_what_was_recorded() {
    let golden = golden();
    assert_eq!(recorded(&guide::index()), golden["guide_index"]["body"]);
}

#[test]
fn the_recorder_digests_only_what_is_long_enough() {
    let short = Value::String("a".repeat(DIGEST_OVER));
    assert_eq!(recorded(&short), short);
    let long = Value::String("a".repeat(DIGEST_OVER + 1));
    assert_eq!(recorded(&long)["chars"], DIGEST_OVER + 1);
}
