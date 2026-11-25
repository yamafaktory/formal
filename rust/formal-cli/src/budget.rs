use std::{
    fs,
    path::{
        Path,
        PathBuf,
    },
};

use formal_lean::{
    env::Env,
    paths::Paths,
};

use crate::check::{
    Paths as CheckPaths,
    check,
};

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

fn checked(case: &Path, scratch: &Path) -> String {
    let spec = fs::read_dir(case)
        .expect("the case is readable")
        .map(|entry| entry.expect("an entry").path())
        .find(|path| {
            path.extension()
                .is_some_and(|extension| extension == "lean")
        })
        .expect("the case has a spec");
    let answers = case.join("answers.json");
    let env = Env::from_pairs(std::env::vars().chain([
        (
            "PROOF_CACHE_DIR".to_string(),
            scratch.join("cache").to_string_lossy().to_string(),
        ),
        (
            "FORMAL_RESULTS_DIR".to_string(),
            scratch.join("results").to_string_lossy().to_string(),
        ),
    ]));
    let (report, _) = check(
        &env,
        &CheckPaths {
            spec: &spec,
            proofs: &case.join("proofs"),
            answers: answers.is_file().then_some(answers.as_path()),
            inputs: None,
        },
    )
    .expect("the case runs");
    format!("{report}\n").replace(&format!("{}/", case.display()), "")
}

#[test]
fn every_case_prints_what_was_recorded() {
    if !lean_is_set_up() {
        return;
    }
    let mut differences = Vec::new();
    for case in cases() {
        let scratch = tempfile::tempdir().expect("a temporary directory");
        let got = checked(&case, scratch.path());
        let want = recorded(&case);
        if got != want {
            differences.push(format!(
                "{}\n--- got\n{got}--- want\n{want}",
                case.display()
            ));
        }
    }
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

#[test]
fn every_case_together_stays_within_the_budget() {
    let budget: toml::Table = fs::read_to_string(fixtures().join("budget.toml"))
        .expect("the budget is readable")
        .parse()
        .expect("the budget is TOML");
    let allowed = budget["bytes"].as_integer().expect("bytes is a number");
    let printed: usize = cases().iter().map(|case| recorded(case).len()).sum();
    assert!(
        i64::try_from(printed).expect("it fits") <= allowed,
        "formal check prints {printed} bytes over the cases, above the budget of {allowed}"
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
