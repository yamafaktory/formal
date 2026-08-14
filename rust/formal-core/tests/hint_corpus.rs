//! Every hint pinned to its text, and every rule in the table reached by a sample.
//!
//! The hints were a 434-line `if ... in data` chain — 16% of the codebase and the
//! single largest thing a rewrite has to reproduce. Unit tests covered the
//! branches someone thought to write one for; this covers all of them. The
//! fixture was built by walking the chain until line and branch coverage of the
//! function were complete, so a refactor that drops, reorders or subtly rewords a
//! rule fails here rather than in front of an agent trying to fix a proof.
//!
//! Now that the rules are data, the corpus does a second job: data rots in a way
//! code does not, because a rule that can never match is not dead code anyone
//! will notice. Every rule must be reached.
//!
//! The hints are recorded as-is, not as assertions about what they ought to say.
//! The question this answers is only "does it still say the same thing".

use std::{
    collections::{
        BTreeMap,
        BTreeSet,
    },
    fs,
    path::PathBuf,
};

use formal_core::hints::Table;
use serde::Deserialize;

/// The sample that nothing in the table claims.
const FALLBACK: &str = "unmatched";

/// The three groups that legitimately share an answer.
///
/// Four different errors are all the same string-prefix limitation, and two
/// branches have an internal fallback for the shape they could not parse.
/// Anything else sharing a hint means a sample is being answered by the wrong
/// branch, which is how a reordering hides a bug.
const EXPECTED_GROUPS: [&[&str]; 4] = [
    &["app_mismatch_bare", "app_mismatch_option_same_inner"],
    &[
        "forward_pattern",
        "free_vars_string",
        "prefix_not_defeq",
        "prefix_unsolved_append",
    ],
    &["function_expected_field", "function_expected_field_word"],
    &["guessed_lemma", "unknown_identifier_unquoted"],
];

#[derive(Deserialize)]
struct Case {
    /// The diagnostic, or nothing at all when Lean reported no error.
    error: Option<String>,
    /// What the advice said when this was recorded.
    hint: String,
}

fn corpus() -> BTreeMap<String, Case> {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/hint_corpus.json");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("{} — {e}", path.display()));
    serde_json::from_str(&text).expect("the corpus is the shape the recorder wrote")
}

fn table() -> &'static Table {
    Table::shipped().expect("the shipped table is valid")
}

#[test]
fn the_corpus_is_the_size_it_was_measured_at() {
    assert_eq!(corpus().len(), 49);
}

#[test]
fn every_recorded_error_still_produces_its_recorded_hint() {
    let table = table();
    let corpus = corpus();
    let changed: Vec<&String> = corpus
        .iter()
        .filter(|(_, case)| {
            case.error
                .as_ref()
                .is_some_and(|error| table.hint_for(error) != case.hint)
        })
        .map(|(name, _)| name)
        .collect();
    assert_eq!(changed, Vec::<&String>::new());
}

#[test]
fn only_the_fallback_sample_falls_through() {
    let corpus = corpus();
    let fallback = &corpus[FALLBACK].hint;
    let fell_through: Vec<&str> = corpus
        .iter()
        .filter(|(_, case)| &case.hint == fallback)
        .map(|(name, _)| name.as_str())
        .collect();
    assert_eq!(fell_through, [FALLBACK]);
}

#[test]
fn no_hint_is_empty_except_for_no_errors() {
    let corpus = corpus();
    let empty: Vec<&str> = corpus
        .iter()
        .filter(|(_, case)| case.hint.is_empty() && case.error.is_some())
        .map(|(name, _)| name.as_str())
        .collect();
    assert_eq!(empty, Vec::<&str>::new());
}

#[test]
fn only_the_known_groups_share_advice() {
    let corpus = corpus();
    let mut by_hint: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (name, case) in &corpus {
        by_hint.entry(&case.hint).or_default().push(name);
    }
    let mut shared: Vec<Vec<&str>> = by_hint
        .into_values()
        .filter(|names| names.len() > 1)
        .collect();
    shared.sort();
    let expected: Vec<Vec<&str>> = EXPECTED_GROUPS.iter().map(|group| group.to_vec()).collect();
    assert_eq!(shared, expected);
}

#[test]
fn every_rule_answers_at_least_one_sample() {
    let table = table();
    let mut fired = BTreeSet::new();
    for case in corpus().values() {
        if let Some(error) = &case.error {
            fired.extend(table.matched_rule_ids(error));
        }
    }
    let unreachable: Vec<String> = table.rule_ids().difference(&fired).cloned().collect();
    assert_eq!(unreachable, Vec::<String>::new());
}
