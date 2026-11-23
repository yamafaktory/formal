//! The specs against the Rust they describe.

use std::{
    path::PathBuf,
    time::Duration,
};

use formal_core::{
    lean_spec::{
        Answer,
        Compared,
        LeanSpec,
        Refutation,
        read_evaluation,
        read_search,
    },
    proof_cache,
    pystr,
};
use formal_lean::{
    run::Runner,
    verifier,
};
use serde_json::{
    Value,
    json,
};

fn runner() -> Option<Runner> {
    let runner = Runner::from_env();
    let project = &runner.paths().lean_project_dir;
    (project.join("lakefile.toml").is_file() && project.join(".lake").is_dir()).then_some(runner)
}

fn spec_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!("../../spec/{name}.lean"))
}

fn spec(name: &str) -> LeanSpec {
    LeanSpec::load(&spec_path(name).to_string_lossy()).expect("the spec loads")
}

fn specs() -> Vec<String> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../spec");
    let mut names: Vec<String> = std::fs::read_dir(dir)
        .expect("the specs are listable")
        .map(|entry| entry.expect("the entry is readable").path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "lean")
        })
        .filter_map(|path| Some(path.file_stem()?.to_string_lossy().to_string()))
        .collect();
    names.sort();
    names
}

fn searched(runner: &Runner, spec: &LeanSpec) -> Vec<Answer> {
    let ids: Vec<&str> = spec.properties.iter().map(String::as_str).collect();
    let search = spec.search(&ids);
    let said = runner
        .verify(&search.lean_code, Some(Duration::from_mins(5)))
        .said();
    read_search(&search, &said)
}

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

fn answer(code: &str, input: &Value) -> Value {
    match code {
        "rust/formal-core/src/pystr.rs is_space" => json!(pystr::is_space(character(input))),
        "core char::is_whitespace" => json!(character(input).is_whitespace()),
        "rust/formal-lean/src/verifier.rs replace_proof" => {
            let pair = input
                .as_array()
                .expect("an input of replace_proof is a pair");
            json!(verifier::replace_proof(text(&pair[0]), text(&pair[1])))
        }
        "rust/formal-lean/src/verifier.rs with_auto_tactics" => {
            json!(verifier::with_auto_tactics(text(input)))
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
        other => panic!("a spec names {other}, which this test does not run"),
    }
}

#[test]
fn the_specs_compare_these_functions() {
    let compared: Vec<(String, String)> = specs()
        .iter()
        .flat_map(|name| spec(name).compared)
        .map(|compared| (compared.function, compared.code))
        .collect();
    let expected = [
        (
            "ProofCache.normaliseCode",
            "rust/formal-core/src/proof_cache.rs normalise_code",
        ),
        (
            "ProofCache.isWordChar",
            "rust/formal-core/src/proof_cache.rs is_word_char",
        ),
        (
            "ProofCache.normaliseFormal",
            "rust/formal-core/src/proof_cache.rs normalise_formal",
        ),
        (
            "ProofCache.normaliseKind",
            "rust/formal-core/src/proof_cache.rs normalise_kind",
        ),
        ("Pystr.isSpace", "rust/formal-core/src/pystr.rs is_space"),
        ("Pystr.rstrip", "rust/formal-core/src/pystr.rs rstrip"),
        ("Pystr.strip", "rust/formal-core/src/pystr.rs strip"),
        (
            "Pystr.splitlines",
            "rust/formal-core/src/pystr.rs splitlines",
        ),
        ("Verifier.isWhitespace", "core char::is_whitespace"),
        (
            "Verifier.replaceProofOn",
            "rust/formal-lean/src/verifier.rs replace_proof",
        ),
        (
            "Verifier.withAutoTactics",
            "rust/formal-lean/src/verifier.rs with_auto_tactics",
        ),
    ];

    let expected: Vec<(String, String)> = expected
        .iter()
        .map(|(function, code)| ((*function).to_string(), (*code).to_string()))
        .collect();
    assert_eq!(compared, expected);
}

#[test]
fn the_rust_answers_what_each_spec_answers() {
    let Some(runner) = runner() else {
        return;
    };
    let mut counts = Vec::new();
    let mut differences = Vec::new();
    for name in specs() {
        let spec = spec(&name);
        let functions: Vec<&str> = spec
            .compared
            .iter()
            .map(|compared| compared.function.as_str())
            .collect();
        let result = runner.verify(&spec.evaluation(&functions), Some(Duration::from_mins(5)));
        assert!(result.success, "{name}: {:?}", result.errors);
        let printed = result.printed();
        let printed: Vec<&str> = printed.iter().map(String::as_str).collect();
        let compared: Vec<&Compared> = spec.compared.iter().collect();
        let evaluated = read_evaluation(&compared, &printed).expect("Lean printed every answer");
        for evaluated in evaluated {
            counts.push((evaluated.function.clone(), evaluated.inputs.len()));
            let rust: Vec<Value> = evaluated
                .inputs
                .iter()
                .map(|input| answer(&evaluated.code, input))
                .collect();
            differences.extend(evaluated.first_difference(&rust).map(|difference| {
                format!(
                    "{} {}: the spec says {}, the Rust says {}",
                    difference.function, difference.input, difference.spec, difference.code
                )
            }));
        }
    }
    let counts: Vec<(&str, usize)> = counts
        .iter()
        .map(|(function, count)| (function.as_str(), *count))
        .collect();
    assert_eq!(
        counts,
        [
            ("ProofCache.normaliseCode", 54_241),
            ("ProofCache.isWordChar", 1_112_064),
            ("ProofCache.normaliseFormal", 22_643),
            ("ProofCache.normaliseKind", 4_681),
            ("Pystr.isSpace", 1_112_064),
            ("Pystr.rstrip", 54_241),
            ("Pystr.strip", 54_241),
            ("Pystr.splitlines", 54_241),
            ("Verifier.isWhitespace", 1_112_064),
            ("Verifier.replaceProofOn", 16_105),
            ("Verifier.withAutoTactics", 4_681),
        ]
    );
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

#[test]
fn lean_answers_the_search_of_every_property_of_every_spec_and_refutes_none() {
    let Some(runner) = runner() else {
        return;
    };
    for name in specs() {
        let spec = spec(&name);
        let searched = searched(&runner, &spec);
        assert_eq!(searched.len(), spec.properties.len(), "{name}");
        assert!(
            searched.iter().all(|answer| *answer == Answer::Unrefuted),
            "{name}: {searched:?}"
        );
    }
}

#[test]
fn a_false_property_comes_back_with_a_counterexample_drawn_from_the_samples() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = tempfile::TempDir::new().expect("a temporary directory");
    let path = dir.path().join("Pystr.lean");
    let text = std::fs::read_to_string(spec_path("Pystr")).expect("the spec reads");
    std::fs::write(
        &path,
        text.replace(
            "end Pystr",
            "def space_is_ascii : Prop := ∀ c : Char, isSpace c = true → c.toNat < 128\n\nend Pystr",
        ),
    )
    .expect("written");
    let spec = LeanSpec::load(&path.to_string_lossy()).expect("the spec loads");
    let refuted: Vec<Refutation> = searched(&runner, &spec)
        .into_iter()
        .filter_map(|answer| match answer {
            Answer::Refuted(refutation) => Some(refutation),
            _ => None,
        })
        .collect();
    let [refutation] = refuted.as_slice() else {
        panic!("one refutation, got {refuted:?}");
    };
    assert_eq!(refutation.id, "Pystr.space_is_ascii");
    assert!(
        refutation.issue.ends_with("< 128 does not hold"),
        "{refutation:?}"
    );
    assert_eq!(refutation.counterexample.len(), 1, "{refutation:?}");
}
