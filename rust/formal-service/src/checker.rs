//! Check caller-supplied Lean proofs.
//!
//! Syntax screening, one batched Lean run, and the recovery chain. An agent that
//! writes its own Lean drives this directly.
//!
//! Two invariants here are not visible from a return value and exist to keep the
//! caller's bill down: a malformed proof must never cost a Mathlib import, and an
//! outcome must never carry the full Lean output.

use std::time::{
    Duration,
    Instant,
};

use formal_core::hints::Table;
use formal_lean::{
    logger::{
        Tag,
        log,
    },
    verifier::{
        BatchEntry,
        LeanResult,
        as_auto_tactic_attempt,
        as_premise_search,
        check_syntax,
        replace_proof,
        suggested_tactic,
    },
};
use serde::Serialize;

/// What the tactic chain gets before it is abandoned.
const AUTO_TACTIC_TIMEOUT: Duration = Duration::from_secs(20);

/// What premise search gets.
///
/// `exact?` searches all of Mathlib. A hit costs about 8s; this caps what a miss
/// can waste, since a miss is pure overhead on top of the retry that follows.
const PREMISE_SEARCH_TIMEOUT: Duration = Duration::from_secs(30);

/// What a caller is told when Lean gave up rather than disagreed.
const NO_DIAGNOSTIC_HINT: &str = "Lean failed without reporting a position, which usually means it crashed or hit a \
                                  limit rather than rejecting the proof: a blown `maxRecDepth`, `maxHeartbeats`, or \
                                  a tactic that diverged. Reduce what the tactic has to chew on — case-split by hand \
                                  instead of `decide` over a large finite type, and prefer `simp only [...]` with \
                                  named lemmas over bare `simp`. Raising the limit usually moves the failure rather \
                                  than removing it.";

/// What a caller is told when the proof never reached Lean.
const SYNTAX_HINT: &str = "The proof was rejected before Lean ran — fix the syntax first.";

/// How much of Lean's output is worth keeping when it named no position.
const OUTPUT_TAIL_LINES: usize = 12;

/// One Lean theorem to check, identified by a caller-chosen id.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Submission {
    /// What the caller knows this proof as.
    pub id: String,
    /// The proof.
    pub lean_code: String,
}

impl Submission {
    /// A proof to check under an id.
    #[must_use]
    pub fn new(id: impl Into<String>, lean_code: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            lean_code: lean_code.into(),
        }
    }
}

/// Whether a proof was accepted.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    /// Lean accepted it.
    Verified,
    /// It was rejected, by Lean or before Lean saw it.
    Failed,
}

/// The verdict on one submission.
///
/// Carries the first error and its hint rather than the full Lean output: a
/// Mathlib failure runs to thousands of tokens, and everything past the first
/// error is noise to whoever has to write the next attempt.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Outcome {
    /// The id it was submitted under.
    pub id: String,
    /// Whether it was accepted.
    pub status: Status,
    /// The proof that was accepted, which is not always the one submitted.
    pub lean_code: String,
    /// The first thing Lean objected to.
    pub error: String,
    /// Where it objected.
    pub line: Option<u32>,
    /// Which column.
    pub col: Option<u32>,
    /// What to do about it.
    pub hint: String,
    /// Whether a Lean verdict is what produced this.
    ///
    /// Set where a [`LeanResult`] becomes an outcome and nowhere else, so a
    /// hand-built outcome — the way a stubbed verifier reaches this code — cannot
    /// claim to have been checked.
    pub checked: bool,
    /// Whether the recovery chain, not the caller, produced the accepted proof.
    pub recovered: bool,
}

impl Outcome {
    /// A verdict that named no Lean run.
    #[must_use]
    pub fn rejected(
        id: impl Into<String>,
        lean_code: impl Into<String>,
        error: impl Into<String>,
        hint: &str,
    ) -> Self {
        Self {
            id: id.into(),
            status: Status::Failed,
            lean_code: lean_code.into(),
            error: error.into(),
            line: None,
            col: None,
            hint: hint.to_string(),
            checked: false,
            recovered: false,
        }
    }

    /// Whether Lean accepted the proof.
    #[must_use]
    pub fn verified(&self) -> bool {
        self.status == Status::Verified
    }
}

/// Whether a verdict has earned a place in the durable cache.
///
/// The cache outlives the run, so a wrong entry is served as truth indefinitely.
/// A session verdict only has to be right now; this has to be evidenced.
#[must_use]
pub fn can_cache(outcome: &Outcome) -> bool {
    outcome.verified()
        && outcome.checked
        && !outcome.lean_code.contains("sorry")
        && check_syntax(&outcome.lean_code).0
}

/// How long something took, for a human reading a log.
#[must_use]
pub fn fmt_elapsed(elapsed: Duration) -> String {
    let seconds = elapsed.as_secs_f64();
    if seconds < 60.0 {
        return format!("{seconds:.1}s");
    }
    let whole = elapsed.as_secs();
    format!("{}m {}s", whole / 60, whole % 60)
}

/// What actually runs Lean.
///
/// A trait so the policy above can be tested without one. Python reached for
/// module-level functions and its tests patched them; the seam is the same, it is
/// just written down.
pub trait Verifier {
    /// Check one proof.
    fn verify(&self, lean_code: &str, timeout: Option<Duration>) -> LeanResult;

    /// Check several in one invocation, or report that it could not be attributed.
    fn verify_batch(
        &self,
        entries: &mut [BatchEntry],
        timeout: Option<Duration>,
    ) -> Option<Vec<(String, LeanResult)>>;
}

impl Verifier for formal_lean::run::Runner {
    fn verify(&self, lean_code: &str, timeout: Option<Duration>) -> LeanResult {
        Self::verify(self, lean_code, timeout)
    }

    fn verify_batch(
        &self,
        entries: &mut [BatchEntry],
        timeout: Option<Duration>,
    ) -> Option<Vec<(String, LeanResult)>> {
        Self::verify_batch(self, entries, timeout)
    }
}

/// The policy around a Lean run: what to screen, what to batch, what to retry.
#[derive(Debug)]
pub struct Checker<'a, V: Verifier> {
    verifier: &'a V,
    table: &'a Table,
}

impl<'a, V: Verifier> Checker<'a, V> {
    /// A checker over a given verifier and hint table.
    #[must_use]
    pub fn new(verifier: &'a V, table: &'a Table) -> Self {
        Self { verifier, table }
    }

    /// Try the tactic chain, then Mathlib premise search, before paying for a retry.
    ///
    /// Nothing when neither closes the goal, in which case the caller's own verdict
    /// stands.
    #[must_use]
    pub fn recover(
        &self,
        entry_id: &str,
        proof_code: &str,
        started_at: Instant,
    ) -> Option<(String, LeanResult)> {
        if let Some(auto_code) = as_auto_tactic_attempt(proof_code) {
            log(
                Tag::Verify,
                &format!("{entry_id} trying auto-tactics before a retry..."),
            );
            let auto_result = self.verifier.verify(&auto_code, Some(AUTO_TACTIC_TIMEOUT));
            if auto_result.success {
                log(
                    Tag::Ok,
                    &format!(
                        "{entry_id} ✓ auto-proved ({})",
                        fmt_elapsed(started_at.elapsed())
                    ),
                );
                return Some((auto_code, auto_result));
            }
        }

        let search_code = as_premise_search(proof_code)?;
        log(
            Tag::Verify,
            &format!("{entry_id} searching Mathlib for a closing lemma..."),
        );
        let search_result = self
            .verifier
            .verify(&search_code, Some(PREMISE_SEARCH_TIMEOUT));
        let tactic = suggested_tactic(&search_result.output)?;

        // Store the concrete term rather than the search tactic: exact? is slow to
        // re-check and its answer can move with Mathlib.
        log(Tag::Lean, &format!("{entry_id} Mathlib suggests: {tactic}"));
        let final_code = replace_proof(proof_code, &tactic)?;
        let final_result = self.verifier.verify(&final_code, None);
        if final_result.success {
            log(
                Tag::Ok,
                &format!(
                    "{entry_id} ✓ proved by premise search ({})",
                    fmt_elapsed(started_at.elapsed())
                ),
            );
            return Some((final_code, final_result));
        }
        search_result
            .success
            .then_some((search_code, search_result))
    }

    fn to_outcome(
        &self,
        entry_id: &str,
        lean_code: &str,
        result: &LeanResult,
        recovered: bool,
    ) -> Outcome {
        let mut outcome = Outcome::rejected(entry_id, lean_code, "", "");
        outcome.checked = true;
        outcome.recovered = recovered;
        if result.success {
            outcome.status = Status::Verified;
            return outcome;
        }

        let Some(error) = result.first_error() else {
            // Lean exited without a diagnostic anyone can act on — a crash, a timeout,
            // a blown recursion limit. Saying "unknown error" and offering no hint left
            // the caller with nothing at all, so hand over whatever Lean did say.
            let lines = result.output.trim().lines().collect::<Vec<_>>();
            let tail = lines[lines.len().saturating_sub(OUTPUT_TAIL_LINES)..].join("\n");
            outcome.error = if tail.is_empty() {
                "Lean produced no output and no diagnostics".to_string()
            } else {
                tail
            };
            outcome.hint = NO_DIAGNOSTIC_HINT.to_string();
            return outcome;
        };

        let (line, col) = error.position();
        outcome.error = if error.data.is_empty() {
            "unknown error".to_string()
        } else {
            error.data.clone()
        };
        outcome.line = line;
        outcome.col = col;
        outcome.hint = result.hint_for_error(self.table);
        outcome
    }

    /// Check every submission, recovering the failures that need no model.
    ///
    /// Syntax is screened first so a malformed proof never costs a Mathlib import.
    /// Whatever survives is checked in a single Lean run; a batch that cannot be
    /// attributed falls back to one run per submission.
    #[must_use]
    pub fn check_batch(
        &self,
        submissions: &[Submission],
        timeout: Option<Duration>,
    ) -> Vec<Outcome> {
        let mut screened: Vec<Outcome> = Vec::new();
        let mut pending: Vec<&Submission> = Vec::new();

        for submission in submissions {
            let (ok, syntax_error) = check_syntax(&submission.lean_code);
            if ok {
                pending.push(submission);
            } else {
                log(
                    Tag::Fail,
                    &format!("{} ✗ syntax error: {syntax_error}", submission.id),
                );
                screened.push(Outcome::rejected(
                    &submission.id,
                    &submission.lean_code,
                    syntax_error,
                    SYNTAX_HINT,
                ));
            }
        }

        let batched = self.batch(&pending, timeout);

        let mut outcomes: Vec<Outcome> = screened;
        for submission in &pending {
            let started_at = Instant::now();
            let mut lean_code = submission.lean_code.clone();
            let mut recovered = false;
            let mut result = batched
                .iter()
                .flatten()
                .find(|(key, _)| key == &submission.id)
                .map_or_else(
                    || self.verifier.verify(&lean_code, timeout),
                    |(_, result)| result.clone(),
                );

            if !result.success
                && let Some((code, recovered_result)) =
                    self.recover(&submission.id, &lean_code, started_at)
            {
                lean_code = code;
                result = recovered_result;
                recovered = true;
            }
            outcomes.push(self.to_outcome(&submission.id, &lean_code, &result, recovered));
        }

        // The caller asked in an order; answer in it.
        let asked: Vec<&str> = submissions
            .iter()
            .map(|submission| submission.id.as_str())
            .collect();
        outcomes.sort_by_key(|outcome| {
            asked
                .iter()
                .position(|id| *id == outcome.id.as_str())
                .unwrap_or(usize::MAX)
        });
        outcomes
    }

    fn batch(
        &self,
        pending: &[&Submission],
        timeout: Option<Duration>,
    ) -> Option<Vec<(String, LeanResult)>> {
        if pending.len() <= 1 {
            return None;
        }
        log(
            Tag::Lean,
            &format!("Checking {} proofs in one Lean run...", pending.len()),
        );
        let mut entries: Vec<BatchEntry> = pending
            .iter()
            .map(|submission| BatchEntry::new(&submission.id, &submission.lean_code))
            .collect();
        let attributed = self.verifier.verify_batch(&mut entries, timeout);
        if attributed.is_none() {
            log(
                Tag::Lean,
                "Batch could not be attributed — verifying individually",
            );
        }
        attributed
    }
}
