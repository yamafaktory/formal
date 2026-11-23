//! The spec against the Rust it describes.

use std::{
    path::PathBuf,
    time::Duration,
};

use formal_core::{
    lean_spec::{
        Compared,
        LeanSpec,
        read_evaluation,
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

fn spec() -> LeanSpec {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../spec/Pystr.lean");
    LeanSpec::load(&path.to_string_lossy()).expect("the spec loads")
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
