//! The spec against the Rust it describes.

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
    pystr,
};
use formal_lean::run::Runner;
use serde_json::{
    Value,
    json,
};

const PYSTR: &str = "rust/formal-core/src/pystr.rs ";

fn runner() -> Option<Runner> {
    let runner = Runner::from_env();
    let project = &runner.paths().lean_project_dir;
    (project.join("lakefile.toml").is_file() && project.join(".lake").is_dir()).then_some(runner)
}

fn spec_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../spec/Pystr.lean")
}

fn spec() -> LeanSpec {
    LeanSpec::load(&spec_path().to_string_lossy()).expect("the spec loads")
}

fn searched(runner: &Runner, spec: &LeanSpec) -> Vec<Answer> {
    let ids: Vec<&str> = spec.properties.iter().map(String::as_str).collect();
    let search = spec.search(&ids);
    let said = runner
        .verify(&search.lean_code, Some(Duration::from_mins(5)))
        .said();
    read_search(&search, &said)
}

fn answer(function: &str, input: &Value) -> Value {
    let text = input.as_str().expect("every input of the spec is text");
    match function {
        "is_space" => {
            let mut chars = text.chars();
            let (Some(c), None) = (chars.next(), chars.next()) else {
                panic!("{text:?} is not one character");
            };
            json!(pystr::is_space(c))
        }
        "strip" => json!(pystr::strip(text)),
        "rstrip" => json!(pystr::rstrip(text)),
        "splitlines" => json!(pystr::splitlines(text)),
        other => panic!("the spec names {other}, which this test does not run"),
    }
}

#[test]
fn the_spec_compares_every_function_of_pystr() {
    let spec = spec();
    let named: Vec<&str> = spec
        .compared
        .iter()
        .map(|compared| compared.code.strip_prefix(PYSTR).unwrap_or(&compared.code))
        .collect();
    assert_eq!(named, ["is_space", "rstrip", "strip", "splitlines"]);
}

#[test]
fn the_rust_answers_what_the_spec_answers() {
    let Some(runner) = runner() else {
        return;
    };
    let spec = spec();
    let functions: Vec<&str> = spec
        .compared
        .iter()
        .map(|compared| compared.function.as_str())
        .collect();
    let result = runner.verify(&spec.evaluation(&functions), Some(Duration::from_mins(5)));
    assert!(result.success, "{:?}", result.errors);
    let printed = result.printed();
    let printed: Vec<&str> = printed.iter().map(String::as_str).collect();
    let compared: Vec<&Compared> = spec.compared.iter().collect();
    let evaluated = read_evaluation(&compared, &printed).expect("Lean printed every answer");

    let counts: Vec<(&str, usize)> = evaluated
        .iter()
        .map(|evaluated| (evaluated.function.as_str(), evaluated.inputs.len()))
        .collect();
    assert_eq!(
        counts,
        [
            ("Pystr.isSpace", 1_112_064),
            ("Pystr.rstrip", 54_241),
            ("Pystr.strip", 54_241),
            ("Pystr.splitlines", 54_241),
        ]
    );

    let differences: Vec<String> = evaluated
        .iter()
        .filter_map(|evaluated| {
            let name = evaluated
                .code
                .strip_prefix(PYSTR)
                .unwrap_or(&evaluated.code);
            let rust: Vec<Value> = evaluated
                .inputs
                .iter()
                .map(|input| answer(name, input))
                .collect();
            evaluated.first_difference(&rust)
        })
        .map(|difference| {
            format!(
                "{} {}: the spec says {}, the Rust says {}",
                difference.function, difference.input, difference.spec, difference.code
            )
        })
        .collect();
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

#[test]
fn lean_answers_the_search_of_every_property_of_the_spec_and_refutes_none() {
    let Some(runner) = runner() else {
        return;
    };
    let spec = spec();
    let searched = searched(&runner, &spec);
    assert_eq!(searched.len(), spec.properties.len());
    assert!(
        searched.iter().all(|answer| *answer == Answer::Unrefuted),
        "{searched:?}"
    );
}

#[test]
fn a_false_property_comes_back_with_a_counterexample_drawn_from_the_samples() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = tempfile::TempDir::new().expect("a temporary directory");
    let path = dir.path().join("Pystr.lean");
    let text = std::fs::read_to_string(spec_path()).expect("the spec reads");
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
