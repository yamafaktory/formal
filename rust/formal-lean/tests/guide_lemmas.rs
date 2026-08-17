//! The guide held to its own advice.
//!
//! It tells callers not to guess lemma names, so it has to be right about the ones
//! it recommends. The filter family went in because a live agent needed it and
//! found nothing, and one name it would have been natural to add —
//! `List.length_filter` — does not exist in this Mathlib at all. A Mathlib bump
//! can invalidate any of them silently.
//!
//! These run Lean, and do nothing where there is none to run.

use std::time::Duration;

use formal_core::guide;
use formal_lean::run::Runner;
use regex::Regex;

/// Names the guide mentions in order to warn that they do not exist.
///
/// Kept out of the existence check, and checked in the other direction below: if
/// Mathlib adds one, the guide's warning about it has become wrong.
const CITED_AS_ABSENT: [&str; 5] = [
    "List.append_inj_iff",
    "List.append_left_cancel",
    "List.append_right_cancel",
    "List.isPrefixOf_append_left",
    "List.length_eq_one",
];

fn runner() -> Option<Runner> {
    let runner = Runner::from_env();
    let project = &runner.paths().lean_project_dir;
    (project.join("lakefile.toml").is_file() && project.join(".lake").is_dir()).then_some(runner)
}

/// Every `List.*` the guide names, minus the ones it names to warn about.
fn recommended() -> Vec<String> {
    let pattern =
        Regex::new(r"List\.[A-Za-z_][A-Za-z0-9_']*[?!]?").expect("the pattern is a literal");
    let text: String = guide::topic_names()
        .into_iter()
        .filter_map(guide::topic)
        .collect();
    let mut names: Vec<String> = pattern
        .find_iter(&text)
        .map(|found| found.as_str().to_string())
        .filter(|name| !CITED_AS_ABSENT.contains(&name.as_str()))
        .collect();
    names.sort();
    names.dedup();
    names
}

#[test]
fn the_guide_names_lemmas_that_exist() {
    let names = recommended();
    assert!(
        !names.is_empty(),
        "no lemma names found — the extraction pattern has drifted"
    );

    let Some(runner) = runner() else {
        return;
    };
    let checks: Vec<String> = names.iter().map(|name| format!("#check @{name}")).collect();
    let result = runner.verify(&format!("import Mathlib\n\n{}\n", checks.join("\n")), None);

    let missing: Vec<String> = result
        .errors
        .iter()
        .map(|error| error.data.replace('\n', " "))
        .collect();
    assert!(
        result.success,
        "the guide recommends lemmas that do not exist: {}",
        missing.join("; ")
    );
}

#[test]
fn the_names_cited_as_absent_are_still_absent() {
    let Some(runner) = runner() else {
        return;
    };
    let mut present = Vec::new();
    for name in CITED_AS_ABSENT {
        let result = runner.verify(
            &format!("import Mathlib\n\n#check @{name}\n"),
            Some(Duration::from_mins(1)),
        );
        if result.success {
            present.push(name);
        }
    }
    assert!(
        present.is_empty(),
        "these now exist, and the guide still warns against them: {}",
        present.join(", ")
    );
}
