//! What formal check prints on the recorded cases, held to its budget.

use std::{
    fs,
    path::{
        Path,
        PathBuf,
    },
    process::Command,
};

use formal_lean::paths::Paths;

fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/check")
}

fn cases() -> Vec<PathBuf> {
    let mut cases: Vec<PathBuf> = fs::read_dir(fixtures())
        .expect("the fixtures are readable")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| path.is_dir())
        .collect();
    cases.sort();
    cases
}

fn recorded(case: &Path) -> String {
    fs::read_to_string(case.join("output.txt")).expect("the case has a recorded output")
}

fn lean_is_set_up() -> bool {
    let project = Paths::from_env().lean_project_dir;
    project.join("lakefile.toml").is_file() && project.join(".lake").is_dir()
}

fn check(case: &Path, scratch: &Path) -> (String, Option<i32>) {
    let spec = fs::read_dir(case)
        .expect("the case is readable")
        .map(|entry| entry.expect("an entry").path())
        .find(|path| {
            path.extension()
                .is_some_and(|extension| extension == "lean")
        })
        .expect("the case has a spec");
    let mut command = Command::new(env!("CARGO_BIN_EXE_formal"));
    command
        .current_dir(case)
        .arg("check")
        .arg(spec.file_name().expect("a file name"))
        .env("PROOF_CACHE_DIR", scratch.join("cache"))
        .env("FORMAL_RESULTS_DIR", scratch.join("results"));
    if case.join("answers.json").is_file() {
        command.args(["--answers", "answers.json"]);
    }
    let output = command.output().expect("formal runs");
    (
        String::from_utf8(output.stdout).expect("the output is text"),
        output.status.code(),
    )
}

#[test]
fn every_case_prints_what_was_recorded() {
    if !lean_is_set_up() {
        return;
    }
    let mut differences = Vec::new();
    for case in cases() {
        let scratch = tempfile::tempdir().expect("a temporary directory");
        let (got, code) = check(&case, scratch.path());
        let want = recorded(&case);
        if got != want || code != Some(1) {
            differences.push(format!(
                "{} exited {code:?}\n--- got\n{got}--- want\n{want}",
                case.display()
            ));
        }
    }
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

#[test]
fn the_budget_is_what_every_case_prints_together() {
    let budget: toml::Table = fs::read_to_string(fixtures().join("budget.toml"))
        .expect("the budget is readable")
        .parse()
        .expect("the budget is TOML");
    let budget = budget["bytes"].as_integer().expect("bytes is a number");
    let printed: usize = cases().iter().map(|case| recorded(case).len()).sum();
    let printed = i64::try_from(printed).expect("it fits");
    assert!(
        printed <= budget,
        "formal check prints {printed} bytes over the cases, above the budget of {budget}"
    );
    assert_eq!(
        printed, budget,
        "the outputs shrank to {printed} bytes: lower the budget to match"
    );
}

#[test]
fn every_case_has_a_recorded_output() {
    let cases = cases();
    assert_ne!(cases.len(), 0);
    for case in cases {
        assert!(case.join("output.txt").is_file(), "{}", case.display());
    }
}
