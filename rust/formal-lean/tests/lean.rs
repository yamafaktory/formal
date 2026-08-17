//! The runner against a real Lean, not a fixture.
//!
//! Nothing else in the port can answer whether formal still checks proofs. These
//! pay a Mathlib import each, so there are few of them and each asks several
//! questions.
//!
//! They do nothing where Lean or the Lake project is not there — a machine that
//! cannot run Lean has no verdict to give.

use std::time::Duration;

use formal_lean::{
    run::Runner,
    verifier::BatchEntry,
};

fn runner() -> Option<Runner> {
    let runner = Runner::from_env();
    let project = &runner.paths().lean_project_dir;
    (project.join("lakefile.toml").is_file() && project.join(".lake").is_dir()).then_some(runner)
}

#[test]
fn lean_accepts_a_true_theorem_and_rejects_a_false_one() {
    let Some(runner) = runner() else {
        return;
    };

    let accepted = runner.verify("import Mathlib\n\ntheorem t : True := trivial\n", None);
    assert!(accepted.success, "{}", accepted.output);
    assert!(accepted.errors.is_empty(), "{:?}", accepted.errors);

    let rejected = runner.verify(
        "import Mathlib\n\ntheorem t : (1 : Nat) = 2 := by rfl\n",
        None,
    );
    assert!(!rejected.success);
    let first = rejected.first_error().expect("Lean said what was wrong");
    assert!(!first.data.is_empty());
    assert_eq!(first.position().0, Some(3), "{first:?}");
}

#[test]
fn a_proof_with_a_hole_in_it_does_not_pass() {
    let Some(runner) = runner() else {
        return;
    };
    let result = runner.verify(
        "import Mathlib\n\ntheorem t : (1 : Nat) = 1 := by sorry\n",
        None,
    );
    assert!(!result.success, "{}", result.output);
    assert!(
        result
            .errors
            .iter()
            .any(|error| error.data.contains("sorry")),
        "{:?}",
        result.errors
    );
}

#[test]
fn a_batch_attributes_each_failure_to_the_proof_that_caused_it() {
    let Some(runner) = runner() else {
        return;
    };
    let mut entries = vec![
        BatchEntry::new("good", "import Mathlib\n\ntheorem good : True := trivial\n"),
        BatchEntry::new(
            "bad",
            "import Mathlib\n\ntheorem bad : (1 : Nat) = 2 := by rfl\n",
        ),
    ];
    let results = runner
        .verify_batch(&mut entries, None)
        .expect("the batch ran");
    let verdicts: Vec<(String, bool)> = results
        .iter()
        .map(|(key, result)| (key.clone(), result.success))
        .collect();
    assert_eq!(
        verdicts,
        [("good".to_string(), true), ("bad".to_string(), false)]
    );

    let failed = &results[1].1;
    let line = failed.first_error().expect("a diagnostic").position().0;
    assert_eq!(
        line,
        Some(3),
        "the position points into the submitted proof, not the batch"
    );
}

#[test]
fn a_run_that_will_not_finish_is_killed_rather_than_waited_on() {
    let Some(runner) = runner() else {
        return;
    };
    let result = runner.verify(
        "import Mathlib\n\ntheorem t : True := by\n  sleep 60000\n  trivial\n",
        Some(Duration::from_secs(2)),
    );
    assert!(!result.success);
    assert!(
        result.output.contains("timed out after 2s"),
        "{}",
        result.output
    );
    assert_eq!(
        result.first_error().map(|e| e.data.as_str()),
        Some("timeout")
    );
}
