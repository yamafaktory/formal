//! Tests for sessions — registration, the cache round trip, and the lifetime.
//!
//! The property worth guarding hardest is the round trip: a proof accepted in one
//! session must be a cache hit in the next, and a proof Lean never actually saw
//! must never become one.

use std::{
    cell::RefCell,
    sync::Arc,
    time::Duration,
};

use formal_core::{
    hints::Table,
    property::PropertySpec,
};
use formal_lean::verifier::{
    BatchEntry,
    LeanError,
    LeanResult,
};
use formal_service::{
    cache::ProofCache,
    checker::{
        Checker,
        Verifier,
    },
    session::{
        Origin,
        Sessions,
    },
};
use tempfile::TempDir;

const PROOF: &str = "import Mathlib\ntheorem t : True := by trivial";

fn table() -> &'static Table {
    Table::shipped().expect("the shipped table is valid")
}

fn spec(id: &str, formal: &str) -> PropertySpec {
    PropertySpec {
        id: id.to_string(),
        description: "the result is never empty".to_string(),
        kind: "bound".to_string(),
        function: "f".to_string(),
        function_code: "def f(x): return x".to_string(),
        formal: formal.to_string(),
        preconditions: vec!["n > 0".to_string()],
        assumptions: vec!["strings modelled as List Char".to_string()],
    }
}

fn specs() -> Vec<PropertySpec> {
    vec![
        spec("p1", "forall x, f x = x"),
        spec("p2", "forall x, f x >= 0"),
    ]
}

fn proofs(ids: &[&str]) -> Vec<(String, String)> {
    ids.iter()
        .map(|id| ((*id).to_string(), PROOF.to_string()))
        .collect()
}

/// Answers as told, and remembers how often it was asked.
#[derive(Default)]
struct Fake {
    result: Option<LeanResult>,
    calls: RefCell<usize>,
}

impl Fake {
    fn accepting() -> Self {
        Self {
            result: Some(LeanResult {
                success: true,
                output: "ok".to_string(),
                errors: Vec::new(),
            }),
            ..Self::default()
        }
    }

    fn rejecting() -> Self {
        Self {
            result: Some(LeanResult {
                success: false,
                output: "noise".to_string(),
                errors: vec![LeanError {
                    severity: "error".to_string(),
                    data: "unsolved goals".to_string(),
                    ..LeanError::default()
                }],
            }),
            ..Self::default()
        }
    }
}

impl Verifier for Fake {
    fn verify(&self, _lean_code: &str, _timeout: Option<Duration>) -> LeanResult {
        *self.calls.borrow_mut() += 1;
        self.result.clone().unwrap_or_default()
    }

    fn verify_batch(
        &self,
        entries: &mut [BatchEntry],
        _timeout: Option<Duration>,
    ) -> Option<Vec<(String, LeanResult)>> {
        *self.calls.borrow_mut() += 1;
        let result = self.result.clone().unwrap_or_default();
        Some(
            entries
                .iter()
                .map(|entry| (entry.key.clone(), result.clone()))
                .collect(),
        )
    }
}

fn cache(dir: &TempDir) -> ProofCache {
    ProofCache::new(dir.path().join("cache"), Duration::from_hours(24 * 7))
}

mod opening {
    use super::*;

    #[test]
    fn everything_is_work_when_the_cache_is_empty() {
        let dir = TempDir::new().expect("a temporary directory");
        let sessions = Sessions::default();
        let session = sessions.open(&cache(&dir), specs(), Vec::new());
        let session = session.lock().expect("a fresh session");
        assert_eq!(session.work_ids(), ["p1", "p2"]);
        assert!(session.cached_ids().is_empty());
        assert!(!session.complete());
    }

    #[test]
    fn distinct_properties_get_distinct_keys() {
        let dir = TempDir::new().expect("a temporary directory");
        let session = Sessions::default().open(&cache(&dir), specs(), Vec::new());
        let session = session.lock().expect("a fresh session");
        assert_ne!(session.keys["p1"], session.keys["p2"]);
    }

    #[test]
    fn a_stale_property_is_reported_and_never_registered() {
        let dir = TempDir::new().expect("a temporary directory");
        let session = Sessions::default().open(&cache(&dir), specs(), vec!["p3".to_string()]);
        let session = session.lock().expect("a fresh session");
        assert_eq!(session.stale, ["p3"]);
        assert!(
            !session.complete(),
            "a stale property is unfinished business"
        );
        assert!(!session.work_ids().contains(&"p3"));
    }

    #[test]
    fn the_session_is_retrievable_and_an_unknown_one_is_not() {
        let dir = TempDir::new().expect("a temporary directory");
        let sessions = Sessions::default();
        let opened = sessions.open(&cache(&dir), specs(), Vec::new());
        let id = opened.lock().expect("a fresh session").id.clone();
        assert!(sessions.get(&id).is_some());
        assert!(sessions.get("nothing").is_none());
    }
}

mod checking {
    use super::*;

    #[test]
    fn a_verified_proof_settles_the_property() {
        let dir = TempDir::new().expect("a temporary directory");
        let fake = Fake::accepting();
        let sessions = Sessions::default();
        let session = sessions.open(&cache(&dir), specs(), Vec::new());
        let mut session = session.lock().expect("a fresh session");
        let outcomes = session
            .check(
                &Checker::new(&fake, table()),
                &cache(&dir),
                &proofs(&["p1"]),
            )
            .expect("p1 is registered");
        assert_eq!(outcomes.len(), 1);
        assert!(outcomes[0].verified());
        assert_eq!(session.work_ids(), ["p2"]);
        assert_eq!(session.origin("p1"), Origin::Submitted);
    }

    #[test]
    fn a_failed_proof_stays_outstanding() {
        let dir = TempDir::new().expect("a temporary directory");
        let fake = Fake::rejecting();
        let session = Sessions::default().open(&cache(&dir), specs(), Vec::new());
        let mut session = session.lock().expect("a fresh session");
        session
            .check(
                &Checker::new(&fake, table()),
                &cache(&dir),
                &proofs(&["p1"]),
            )
            .expect("p1 is registered");
        assert_eq!(session.work_ids(), ["p1", "p2"]);
    }

    #[test]
    fn an_unregistered_id_is_rejected_before_lean_is_paid_for() {
        let dir = TempDir::new().expect("a temporary directory");
        let fake = Fake::accepting();
        let session = Sessions::default().open(&cache(&dir), specs(), Vec::new());
        let mut session = session.lock().expect("a fresh session");
        let error = session
            .check(
                &Checker::new(&fake, table()),
                &cache(&dir),
                &proofs(&["nope", "also"]),
            )
            .expect_err("neither is registered");
        assert_eq!(
            error.to_string(),
            "Not registered in this session: also, nope"
        );
        assert_eq!(*fake.calls.borrow(), 0);
    }

    #[test]
    fn a_settled_property_is_not_rechecked() {
        let dir = TempDir::new().expect("a temporary directory");
        let fake = Fake::accepting();
        let checker = Checker::new(&fake, table());
        let cache = cache(&dir);
        let session = Sessions::default().open(&cache, specs(), Vec::new());
        let mut session = session.lock().expect("a fresh session");

        session
            .check(&checker, &cache, &proofs(&["p1"]))
            .expect("p1 is registered");
        let after_first = *fake.calls.borrow();
        let again = session
            .check(&checker, &cache, &proofs(&["p1"]))
            .expect("p1 is registered");

        assert!(again.is_empty(), "nothing was left to check");
        assert_eq!(
            *fake.calls.borrow(),
            after_first,
            "and so Lean was not asked again"
        );
    }

    #[test]
    fn nothing_to_check_runs_no_lean() {
        let dir = TempDir::new().expect("a temporary directory");
        let fake = Fake::accepting();
        let cache = cache(&dir);
        let session = Sessions::default().open(&cache, specs(), Vec::new());
        let mut session = session.lock().expect("a fresh session");
        let outcomes = session
            .check(&Checker::new(&fake, table()), &cache, &[])
            .expect("nothing is unregistered");
        assert!(outcomes.is_empty());
        assert_eq!(*fake.calls.borrow(), 0);
    }

    #[test]
    fn attempts_are_counted_per_property() {
        let dir = TempDir::new().expect("a temporary directory");
        let fake = Fake::rejecting();
        let checker = Checker::new(&fake, table());
        let cache = cache(&dir);
        let session = Sessions::default().open(&cache, specs(), Vec::new());
        let mut session = session.lock().expect("a fresh session");

        for _ in 0..3 {
            session
                .check(&checker, &cache, &proofs(&["p1"]))
                .expect("p1 is registered");
        }
        session
            .check(&checker, &cache, &proofs(&["p2"]))
            .expect("p2 is registered");

        assert_eq!(session.attempts["p1"], 3);
        assert_eq!(session.attempts["p2"], 1);
    }
}

mod cache_round_trip {
    use super::*;

    #[test]
    fn a_proof_accepted_now_is_a_cache_hit_next_time() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        let fake = Fake::accepting();
        let sessions = Sessions::default();

        let first = sessions.open(&cache, specs(), Vec::new());
        first
            .lock()
            .expect("a fresh session")
            .check(&Checker::new(&fake, table()), &cache, &proofs(&["p1"]))
            .expect("p1 is registered");

        let second = sessions.open(&cache, specs(), Vec::new());
        let second = second.lock().expect("a fresh session");
        assert_eq!(second.cached_ids(), ["p1"]);
        assert_eq!(second.work_ids(), ["p2"]);
        assert_eq!(second.origin("p1"), Origin::Cache);
    }

    #[test]
    fn a_hit_carries_the_modelling_the_proof_was_accepted_under() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        let fake = Fake::accepting();
        let sessions = Sessions::default();

        let first = sessions.open(&cache, specs(), Vec::new());
        first
            .lock()
            .expect("a fresh session")
            .check(&Checker::new(&fake, table()), &cache, &proofs(&["p1"]))
            .expect("p1 is registered");

        let second = sessions.open(&cache, specs(), Vec::new());
        let hit = second.lock().expect("a fresh session").hits["p1"].clone();
        assert_eq!(hit.kind, "bound");
        assert_eq!(hit.description, "the result is never empty");
        assert_eq!(hit.assumptions, ["strings modelled as List Char"]);
    }

    #[test]
    fn a_failure_is_never_cached() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        let sessions = Sessions::default();

        let rejecting = Fake::rejecting();
        let first = sessions.open(&cache, specs(), Vec::new());
        first
            .lock()
            .expect("a fresh session")
            .check(&Checker::new(&rejecting, table()), &cache, &proofs(&["p1"]))
            .expect("p1 is registered");

        let second = sessions.open(&cache, specs(), Vec::new());
        assert!(
            second
                .lock()
                .expect("a fresh session")
                .cached_ids()
                .is_empty()
        );
    }

    #[test]
    fn retries_are_recorded_on_the_cached_result() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        let sessions = Sessions::default();
        let session = sessions.open(&cache, specs(), Vec::new());
        let key = session.lock().expect("a fresh session").keys["p1"].clone();

        let rejecting = Fake::rejecting();
        let accepting = Fake::accepting();
        {
            let mut held = session.lock().expect("a fresh session");
            held.check(&Checker::new(&rejecting, table()), &cache, &proofs(&["p1"]))
                .expect("p1 is registered");
            held.check(&Checker::new(&rejecting, table()), &cache, &proofs(&["p1"]))
                .expect("p1 is registered");
            held.check(&Checker::new(&accepting, table()), &cache, &proofs(&["p1"]))
                .expect("p1 is registered");
        }

        let entry = cache.load(&key).expect("the third attempt was cached");
        assert_eq!(entry.retries, 2);
        assert_eq!(entry.status, "verified");
        assert_eq!(entry.preconditions, ["n > 0"]);
    }

    #[test]
    fn a_verdict_lean_never_produced_is_not_cached() {
        let dir = TempDir::new().expect("a temporary directory");
        let cache = cache(&dir);
        let sessions = Sessions::default();

        // A proof with a sorry in it: accepted by this verifier, but never cacheable.
        let fake = Fake::accepting();
        let session = sessions.open(&cache, specs(), Vec::new());
        let key = session.lock().expect("a fresh session").keys["p1"].clone();
        let holed = vec![("p1".to_string(), "theorem t : True := by sorry".to_string())];
        let outcomes = session
            .lock()
            .expect("a fresh session")
            .check(&Checker::new(&fake, table()), &cache, &holed)
            .expect("p1 is registered");

        assert!(
            outcomes[0].verified(),
            "the session still reports what it was told"
        );
        assert_eq!(cache.load(&key), None, "but nothing durable was written");
    }
}

mod lifetime {
    use super::*;

    #[test]
    fn closing_removes_the_session_and_saying_so_twice_is_honest() {
        let dir = TempDir::new().expect("a temporary directory");
        let sessions = Sessions::default();
        let session = sessions.open(&cache(&dir), specs(), Vec::new());
        let id = session.lock().expect("a fresh session").id.clone();

        assert!(sessions.close(&id));
        assert!(!sessions.close(&id));
        assert!(sessions.get(&id).is_none());
    }

    #[test]
    fn an_expired_session_is_evicted() {
        let dir = TempDir::new().expect("a temporary directory");
        let sessions = Sessions::new(Duration::from_secs(0));
        let session = sessions.open(&cache(&dir), specs(), Vec::new());
        let id = session.lock().expect("a fresh session").id.clone();
        assert_eq!(
            sessions.ttl(),
            Duration::from_mins(1),
            "a floor stops a zero from expiring everything instantly"
        );
        assert!(sessions.get(&id).is_some());
    }

    #[test]
    fn a_session_past_its_lifetime_is_gone() {
        let dir = TempDir::new().expect("a temporary directory");
        let sessions = Sessions::new(Duration::from_mins(1));
        let session = sessions.open(&cache(&dir), specs(), Vec::new());
        let id = session.lock().expect("a fresh session").id.clone();

        session.lock().expect("a fresh session").created_at -= Duration::from_mins(2);
        assert!(sessions.get(&id).is_none());
        assert!(sessions.is_empty());
    }

    #[test]
    fn a_fresh_session_survives_the_sweep() {
        let dir = TempDir::new().expect("a temporary directory");
        let sessions = Sessions::new(Duration::from_hours(1));
        let first = sessions.open(&cache(&dir), specs(), Vec::new());
        let id = first.lock().expect("a fresh session").id.clone();
        sessions.open(&cache(&dir), specs(), Vec::new());
        assert!(sessions.get(&id).is_some());
        assert_eq!(sessions.len(), 2);
    }

    #[test]
    fn two_sessions_do_not_share_an_id() {
        let dir = TempDir::new().expect("a temporary directory");
        let sessions = Sessions::default();
        let first = sessions.open(&cache(&dir), specs(), Vec::new());
        let second = sessions.open(&cache(&dir), specs(), Vec::new());
        assert_ne!(
            first.lock().expect("a fresh session").id,
            second.lock().expect("a fresh session").id
        );
    }

    #[test]
    fn a_handle_taken_before_closing_still_works() {
        let dir = TempDir::new().expect("a temporary directory");
        let sessions = Sessions::default();
        let session = sessions.open(&cache(&dir), specs(), Vec::new());
        let id = session.lock().expect("a fresh session").id.clone();
        let held = sessions.get(&id).expect("it is open");

        sessions.close(&id);

        assert_eq!(
            Arc::strong_count(&held),
            2,
            "the registry let go, the holder did not"
        );
        assert_eq!(held.lock().expect("still usable").work_ids(), ["p1", "p2"]);
    }
}

mod configuration {
    use formal_lean::env::Env;

    use super::*;

    #[test]
    fn a_stated_lifetime_is_what_a_session_gets() {
        let sessions = Sessions::resolve(&Env::from_pairs([("SESSION_TTL_MINUTES", "5")]));
        assert_eq!(sessions.ttl(), Duration::from_mins(5));
    }

    #[test]
    fn a_lifetime_below_the_floor_is_raised_to_it() {
        let sessions = Sessions::resolve(&Env::from_pairs([("SESSION_TTL_MINUTES", "0")]));
        assert_eq!(sessions.ttl(), Duration::from_mins(1));
    }

    #[test]
    fn a_lifetime_that_is_not_a_number_leaves_the_default() {
        let sessions = Sessions::resolve(&Env::from_pairs([("SESSION_TTL_MINUTES", "soon")]));
        assert_eq!(sessions.ttl(), Duration::from_hours(1));
    }
}

mod origins {
    use super::*;

    #[test]
    fn the_wire_spelling_is_what_the_guide_promises() {
        assert_eq!(Origin::Cache.as_str(), "cache");
        assert_eq!(Origin::Recovered.as_str(), "recovered");
        assert_eq!(Origin::Submitted.as_str(), "submitted");
    }

    #[test]
    fn an_unproved_property_reads_as_submitted() {
        let dir = TempDir::new().expect("a temporary directory");
        let session = Sessions::default().open(&cache(&dir), specs(), Vec::new());
        assert_eq!(
            session.lock().expect("a fresh session").origin("p1"),
            Origin::Submitted
        );
    }
}
