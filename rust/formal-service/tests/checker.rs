//! Tests for the checker — the core an agent drives directly.
//!
//! Two invariants matter here beyond correctness: a malformed proof must never
//! cost a Mathlib import, and an outcome must never carry the full Lean output.
//! Both exist to keep the caller's token bill down, and neither is visible from
//! the return value — so both are asserted on what the verifier was asked, not on
//! what came back.

use std::{
    cell::RefCell,
    time::Duration,
};

use formal_core::hints::Table;
use formal_lean::verifier::{
    BatchEntry,
    LeanError,
    LeanResult,
    Pos,
};
use formal_service::checker::{
    Checker,
    Outcome,
    Status,
    Submission,
    Verifier,
    can_cache,
    fmt_elapsed,
};

const PROOF: &str = "import Mathlib\ntheorem t : True := by trivial";

fn table() -> &'static Table {
    Table::shipped().expect("the shipped table is valid")
}

fn ok() -> LeanResult {
    LeanResult {
        success: true,
        output: "ok".to_string(),
        errors: Vec::new(),
    }
}

fn fail(data: &str, line: u32, col: u32, output: &str) -> LeanResult {
    LeanResult {
        success: false,
        output: output.to_string(),
        errors: vec![LeanError {
            severity: "error".to_string(),
            data: data.to_string(),
            pos: Some(Pos {
                line: Some(line),
                column: Some(col),
            }),
            ..LeanError::default()
        }],
    }
}

fn rejected() -> LeanResult {
    fail(
        "unknown identifier 'foo'",
        3,
        7,
        "…thousands of tokens of Mathlib noise…",
    )
}

fn subs(ids: &[&str]) -> Vec<Submission> {
    ids.iter()
        .map(|id| Submission::new(*id, format!("theorem {id} : True := by trivial")))
        .collect()
}

/// A verifier that answers as told and remembers what it was asked.
#[derive(Default)]
struct Fake {
    single: Option<LeanResult>,
    batch: Option<Vec<(String, LeanResult)>>,
    /// Every proof handed to `verify`, in order.
    verified: RefCell<Vec<String>>,
    /// Every set of keys handed to `verify_batch`, in order.
    batched: RefCell<Vec<Vec<String>>>,
}

impl Fake {
    fn answering(result: LeanResult) -> Self {
        Self {
            single: Some(result),
            ..Self::default()
        }
    }

    fn batching(pairs: &[(&str, LeanResult)]) -> Self {
        Self {
            batch: Some(
                pairs
                    .iter()
                    .map(|(key, r)| ((*key).to_string(), r.clone()))
                    .collect(),
            ),
            ..Self::default()
        }
    }

    fn verify_calls(&self) -> usize {
        self.verified.borrow().len()
    }

    fn batch_calls(&self) -> usize {
        self.batched.borrow().len()
    }
}

impl Verifier for Fake {
    fn verify(&self, lean_code: &str, _timeout: Option<Duration>) -> LeanResult {
        self.verified.borrow_mut().push(lean_code.to_string());
        self.single.clone().unwrap_or_else(ok)
    }

    fn verify_batch(
        &self,
        entries: &mut [BatchEntry],
        _timeout: Option<Duration>,
    ) -> Option<Vec<(String, LeanResult)>> {
        self.batched
            .borrow_mut()
            .push(entries.iter().map(|entry| entry.key.clone()).collect());
        self.batch.clone()
    }
}

fn check(fake: &Fake, submissions: &[Submission]) -> Vec<Outcome> {
    Checker::new(fake, table()).check_batch(submissions, None)
}

mod syntax_screening {
    use super::*;

    #[test]
    fn a_malformed_proof_never_reaches_lean() {
        let fake = Fake::default();
        let outcomes = check(&fake, &[Submission::new("p1", "x + 1 = 2")]);
        assert_eq!(fake.verify_calls(), 0);
        assert_eq!(fake.batch_calls(), 0);
        assert_eq!(outcomes[0].status, Status::Failed);
        assert!(
            outcomes[0].error.contains("must contain at least one of"),
            "{:?}",
            outcomes[0]
        );
    }

    #[test]
    fn only_the_malformed_one_is_screened_out() {
        let fake = Fake::default();
        let submissions = vec![
            Submission::new("p1", "theorem p1 : True := by trivial"),
            Submission::new("p2", "not a proof at all"),
            Submission::new("p3", "theorem p3 : True := by trivial"),
        ];
        let outcomes = check(&fake, &submissions);
        let statuses: Vec<Status> = outcomes.iter().map(|outcome| outcome.status).collect();
        assert_eq!(
            statuses,
            [Status::Verified, Status::Failed, Status::Verified]
        );
    }

    #[test]
    fn a_screened_proof_is_not_marked_as_checked() {
        let outcomes = check(&Fake::default(), &[Submission::new("p1", "x + 1 = 2")]);
        assert!(
            !outcomes[0].checked,
            "nothing checked it, so it cannot be cached"
        );
    }
}

mod batching {
    use super::*;

    #[test]
    fn many_proofs_share_one_lean_run() {
        let fake = Fake::batching(&[("p1", ok()), ("p2", ok())]);
        let outcomes = check(&fake, &subs(&["p1", "p2"]));
        assert_eq!(fake.batch_calls(), 1);
        assert_eq!(fake.verify_calls(), 0);
        assert!(outcomes.iter().all(Outcome::verified));
    }

    #[test]
    fn a_single_proof_skips_the_batch() {
        let fake = Fake::answering(ok());
        check(&fake, &subs(&["p1"]));
        assert_eq!(fake.batch_calls(), 0);
        assert_eq!(fake.verify_calls(), 1);
    }

    #[test]
    fn an_unattributable_batch_falls_back_to_one_run_each() {
        let fake = Fake::answering(ok());
        let outcomes = check(&fake, &subs(&["p1", "p2"]));
        assert_eq!(fake.batch_calls(), 1);
        assert_eq!(fake.verify_calls(), 2);
        assert!(outcomes.iter().all(Outcome::verified));
    }
}

mod outcomes {
    use super::*;

    #[test]
    fn a_failure_carries_the_first_error_and_its_hint() {
        let fake = Fake::answering(fail("no goals", 4, 2, "noise"));
        let outcome = check(&fake, &subs(&["p1"])).remove(0);
        assert_eq!(outcome.status, Status::Failed);
        assert_eq!(outcome.error, "no goals");
        assert_eq!((outcome.line, outcome.col), (Some(4), Some(2)));
        assert!(!outcome.hint.is_empty());
    }

    #[test]
    fn a_failure_omits_the_full_lean_output() {
        let noise = "x".repeat(5000);
        let fake = Fake::answering(fail("no goals", 1, 1, &noise));
        let outcome = check(&fake, &subs(&["p1"])).remove(0);
        assert!(!format!("{outcome:?}").contains(&noise));
    }

    #[test]
    fn a_failure_with_no_diagnostic_hands_over_what_lean_did_say() {
        let output = (1..=20)
            .map(|n| format!("line {n}"))
            .collect::<Vec<_>>()
            .join("\n");
        let fake = Fake::answering(LeanResult {
            success: false,
            output,
            errors: Vec::new(),
        });
        let outcome = check(&fake, &subs(&["p1"])).remove(0);
        assert_eq!(outcome.error.lines().count(), 12, "{}", outcome.error);
        assert!(outcome.error.starts_with("line 9"), "{}", outcome.error);
        assert!(outcome.hint.contains("maxRecDepth"), "{}", outcome.hint);
        assert_eq!((outcome.line, outcome.col), (None, None));
    }

    #[test]
    fn a_failure_with_neither_diagnostic_nor_output_still_says_something() {
        let fake = Fake::answering(LeanResult::default());
        let outcome = check(&fake, &subs(&["p1"])).remove(0);
        assert_eq!(outcome.error, "Lean produced no output and no diagnostics");
    }

    #[test]
    fn the_order_matches_the_submissions() {
        let fake = Fake::answering(ok());
        let submissions = vec![
            Submission::new("p1", "theorem p1 : True := by trivial"),
            Submission::new("p2", "not a proof at all"),
            Submission::new("p3", "theorem p3 : True := by trivial"),
        ];
        let ids: Vec<String> = check(&fake, &submissions)
            .into_iter()
            .map(|o| o.id)
            .collect();
        assert_eq!(ids, ["p1", "p2", "p3"]);
    }

    #[test]
    fn a_verified_proof_reports_no_error() {
        let fake = Fake::answering(ok());
        let outcome = check(&fake, &subs(&["p1"])).remove(0);
        assert!(outcome.verified());
        assert_eq!(outcome.error, "");
        assert_eq!(outcome.hint, "");
    }
}

mod recovery {
    use super::*;

    /// A verifier that rejects the submission and accepts the tactic chain.
    #[derive(Default)]
    struct Recovering {
        seen: RefCell<Vec<String>>,
    }

    impl Verifier for Recovering {
        fn verify(&self, lean_code: &str, _timeout: Option<Duration>) -> LeanResult {
            self.seen.borrow_mut().push(lean_code.to_string());
            if lean_code.contains("first |") {
                ok()
            } else {
                rejected()
            }
        }

        fn verify_batch(
            &self,
            _entries: &mut [BatchEntry],
            _timeout: Option<Duration>,
        ) -> Option<Vec<(String, LeanResult)>> {
            None
        }
    }

    #[test]
    fn a_recovered_proof_replaces_the_submission() {
        let fake = Recovering::default();
        let outcome = Checker::new(&fake, table())
            .check_batch(&subs(&["p1"]), None)
            .remove(0);
        assert_eq!(outcome.status, Status::Verified);
        assert!(
            outcome.lean_code.contains("first |"),
            "{}",
            outcome.lean_code
        );
        assert!(outcome.recovered);
    }

    #[test]
    fn recovery_is_not_attempted_on_success() {
        let fake = Fake::answering(ok());
        let outcome = check(&fake, &subs(&["p1"])).remove(0);
        assert_eq!(fake.verify_calls(), 1, "{:?}", fake.verified.borrow());
        assert!(!outcome.recovered);
    }

    #[test]
    fn a_failed_recovery_leaves_the_original_verdict() {
        let fake = Fake::answering(fail("still broken", 1, 1, "noise"));
        let outcome = check(&fake, &subs(&["p1"])).remove(0);
        assert_eq!(outcome.status, Status::Failed);
        assert_eq!(outcome.error, "still broken");
        assert!(!outcome.recovered);
    }
}

mod elapsed {
    use super::*;

    #[test]
    fn under_a_minute_is_tenths_of_a_second() {
        assert_eq!(fmt_elapsed(Duration::from_millis(3140)), "3.1s");
    }

    #[test]
    fn over_a_minute_is_minutes_and_seconds() {
        assert_eq!(fmt_elapsed(Duration::from_secs(125)), "2m 5s");
        assert_eq!(fmt_elapsed(Duration::from_mins(1)), "1m 0s");
    }
}

mod caching {
    use super::*;

    fn outcome() -> Outcome {
        Outcome {
            id: "p1".to_string(),
            status: Status::Verified,
            lean_code: PROOF.to_string(),
            error: String::new(),
            line: None,
            col: None,
            hint: String::new(),
            checked: true,
            recovered: false,
        }
    }

    #[test]
    fn an_evidenced_proof_can_be_cached() {
        assert!(can_cache(&outcome()));
    }

    #[test]
    fn a_failure_can_never_be_cached() {
        assert!(!can_cache(&Outcome {
            status: Status::Failed,
            ..outcome()
        }));
    }

    #[test]
    fn an_unchecked_verdict_can_never_be_cached() {
        assert!(!can_cache(&Outcome {
            checked: false,
            ..outcome()
        }));
    }

    #[test]
    fn a_proof_containing_sorry_can_never_be_cached() {
        assert!(!can_cache(&Outcome {
            lean_code: "theorem t : True := by sorry".to_string(),
            ..outcome()
        }));
    }

    #[test]
    fn a_proof_that_would_not_pass_screening_can_never_be_cached() {
        assert!(!can_cache(&Outcome {
            lean_code: "x + 1 = 2".to_string(),
            ..outcome()
        }));
    }

    #[test]
    fn the_status_is_written_as_the_api_says_it() {
        assert_eq!(
            serde_json::to_string(&Status::Verified).expect("it serialises"),
            "\"verified\""
        );
        assert_eq!(
            serde_json::to_string(&Status::Failed).expect("it serialises"),
            "\"failed\""
        );
    }
}
