//! Answer for the functions a spec compares, with formal's own code:
//! `answers <spec> <inputs.json> <answers.json>`. formal's CI gives it to the GitHub
//! Action as its `answers` command.

use std::{
    env,
    fs,
    process::ExitCode,
};

use formal_core::lean_spec::LeanSpec;
use serde_json::{
    Map,
    Value,
};

#[path = "../tests/support/answer.rs"]
mod answer;

fn main() -> ExitCode {
    let arguments: Vec<String> = env::args().skip(1).collect();
    let [spec, inputs, answers] = arguments.as_slice() else {
        eprintln!("usage: answers <spec> <inputs.json> <answers.json>");
        return ExitCode::from(2);
    };
    let spec = fs::canonicalize(spec).expect("the spec exists");
    let spec = LeanSpec::load(&spec.to_string_lossy()).expect("the spec loads");
    let inputs: Map<String, Value> =
        serde_json::from_str(&fs::read_to_string(inputs).expect("the inputs are readable"))
            .expect("the inputs are JSON");
    let answered: Map<String, Value> = spec
        .compared
        .iter()
        .filter_map(|compared| {
            let given = inputs.get(&compared.function)?.as_array()?;
            let found = given
                .iter()
                .map(|input| answer::answer(&compared.code, input))
                .collect();
            Some((compared.function.clone(), Value::Array(found)))
        })
        .collect();
    fs::write(answers, Value::Object(answered).to_string()).expect("the answers are written");
    ExitCode::SUCCESS
}
