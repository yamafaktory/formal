use formal_core::{
    proof_cache,
    pystr,
};
use formal_lean::verifier;
use serde_json::{
    Value,
    json,
};

fn text(input: &Value) -> &str {
    input.as_str().expect("every input of the specs is text")
}

fn character(input: &Value) -> char {
    let mut chars = text(input).chars();
    let (Some(c), None) = (chars.next(), chars.next()) else {
        panic!("{input} is not one character");
    };
    c
}

pub(crate) fn answer(code: &str, input: &Value) -> Value {
    match code {
        "rust/formal-core/src/pystr.rs is_space" => json!(pystr::is_space(character(input))),
        "core char::is_whitespace" => json!(character(input).is_whitespace()),
        "rust/formal-lean/src/verifier.rs replace_proof" => {
            let pair = input
                .as_array()
                .expect("an input of replace_proof is a pair");
            json!(verifier::replace_proof(text(&pair[0]), text(&pair[1])))
        }
        "rust/formal-core/src/proof_cache.rs is_word_char" => {
            json!(proof_cache::is_word_char(character(input)))
        }
        "rust/formal-core/src/proof_cache.rs normalise_kind" => {
            json!(proof_cache::normalise_kind(text(input)))
        }
        "rust/formal-core/src/pystr.rs strip" => json!(pystr::strip(text(input))),
        "rust/formal-core/src/pystr.rs rstrip" => json!(pystr::rstrip(text(input))),
        "rust/formal-core/src/pystr.rs splitlines" => json!(pystr::splitlines(text(input))),
        "rust/formal-core/src/proof_cache.rs normalise_code" => {
            json!(proof_cache::normalise_code(text(input)))
        }
        "rust/formal-core/src/proof_cache.rs normalise_formal" => {
            json!(proof_cache::normalise_formal(text(input)))
        }
        other => panic!("a spec names {other}, which formal does not answer for"),
    }
}
