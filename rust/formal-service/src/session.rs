//! Sessions for caller-supplied proofs.
//!
//! A session holds the property metadata once, so a retry carries only Lean. The
//! caller registers what it intends to prove, learns which properties the cache
//! has already settled, and then submits proofs by id until nothing is left
//! failing.
//!
//! Registering is also what makes the cache work in both directions: the key is
//! derived from the material the property is made of, so a proof written now is a
//! cache hit for a later run, and the reverse.

use std::{
    collections::HashMap,
    sync::{
        Arc,
        Mutex,
    },
    time::{
        Duration,
        Instant,
    },
};

use formal_core::{
    lean_spec::{
        Answer,
        Compared,
        Difference,
        Evaluated,
        LeanSpec,
        Refutation,
        read_evaluation,
        read_search,
    },
    property::{
        PropertyResult,
        PropertySpec,
    },
};
use formal_lean::{
    env::Env,
    logger::{
        Tag,
        log,
    },
};
use thiserror::Error;
use uuid::Uuid;

use crate::{
    cache::ProofCache,
    checker::{
        Checker,
        Outcome,
        Submission,
        Verifier,
        can_cache,
    },
};

/// How long an idle session survives, and the least it can be set to.
const DEFAULT_TTL: Duration = Duration::from_hours(1);

/// The floor `SESSION_TTL_MINUTES` is clamped to.
const MINIMUM_TTL: Duration = Duration::from_mins(1);

/// A proof was submitted for an id the session never registered.
#[derive(Clone, Debug, Error)]
#[error("Not registered in this session: {}", ids.join(", "))]
pub struct UnknownProperty {
    /// The ids that are not in the session, sorted.
    pub ids: Vec<String>,
}

/// Why the code's answers could not be compared with the spec's.
#[derive(Clone, Debug, Error)]
pub enum CompareError {
    /// The session compares no function under these names.
    #[error("Not compared in this session: {}", .0.join(", "))]
    Unknown(Vec<String>),
    /// The code gave a different number of answers than the spec has inputs.
    #[error("{function}: {answers} answers for {inputs} inputs")]
    Count {
        /// The function.
        function: String,
        /// How many answers the code gave.
        answers: usize,
        /// How many inputs the spec has.
        inputs: usize,
    },
    /// Lean did not print the spec's answers.
    #[error("Lean could not evaluate the inputs of the spec: {0}")]
    Evaluation(String),
    /// Lean gave no verdict on the spec, because formal could not run it.
    #[error("formal could not run Lean on the spec: {0}")]
    Unrun(String),
}

/// What came of comparing the code's answers with the spec's.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Comparison {
    /// The functions whose code answers what the spec answers on every input.
    pub matched: Vec<String>,
    /// The functions whose code differs, with the first input where it does.
    pub differed: Vec<Difference>,
}

/// What a cached proof actually established, so a caller can reject a mismatch.
///
/// The key covers the function, the kind and the formal statement — not the prose
/// that came with them. Two callers can therefore agree on a statement while
/// modelling it differently, so the modelling recorded when the proof was accepted
/// travels back with the hit rather than being taken on trust.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CacheHit {
    /// The property it settles.
    pub id: String,
    /// How it was described when it was proved.
    pub description: String,
    /// What kind of claim it was.
    pub kind: String,
    /// How the code was modelled in Lean.
    pub assumptions: Vec<String>,
}

/// Where an accepted proof came from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Origin {
    /// It was already proved, before this session opened.
    Cache,
    /// The recovery chain produced it, not the caller.
    Recovered,
    /// The caller wrote it.
    Submitted,
}

impl Origin {
    /// How the wire spells it.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Cache => "cache",
            Self::Recovered => "recovered",
            Self::Submitted => "submitted",
        }
    }
}

/// One caller's run: what it means to prove, and how far it has got.
#[derive(Clone, Debug)]
pub struct Session {
    /// What the caller refers to it as.
    pub id: String,
    /// When it opened, for the idle timeout.
    pub created_at: Instant,
    /// The properties, in the order they were registered.
    pub specs: Vec<PropertySpec>,
    /// The cache key of each, by id.
    pub keys: HashMap<String, String>,
    /// The accepted Lean for each settled property, by id.
    pub verified: HashMap<String, String>,
    /// How many times each property has been submitted.
    pub attempts: HashMap<String, u32>,
    /// What the cache already knew, by id.
    pub hits: HashMap<String, CacheHit>,
    /// Ids reported rather than registered, because their source moved.
    pub stale: Vec<String>,
    /// Ids whose accepted proof came from the recovery chain.
    ///
    /// Without this a caller cannot tell whether its own tactic worked, and the
    /// proof that gets cached is the accepted one, not the submitted one.
    pub recovered: Vec<String>,
    /// The Lean spec every proof is checked against, when the session opened on one.
    pub lean_spec: Option<LeanSpec>,
    /// The inputs and the spec's answers for each compared function, once Lean printed them.
    pub evaluated: Vec<Evaluated>,
    /// The properties of the Lean spec the search found a counterexample to.
    pub refuted: Vec<Refutation>,
}

impl Session {
    fn spec(&self, property_id: &str) -> Option<&PropertySpec> {
        self.specs.iter().find(|spec| spec.id == property_id)
    }

    fn registered(&self, property_id: &str) -> bool {
        self.spec(property_id).is_some()
    }

    /// Where the accepted proof for a property came from.
    #[must_use]
    pub fn origin(&self, property_id: &str) -> Origin {
        if self.hits.contains_key(property_id) {
            return Origin::Cache;
        }
        if self.recovered.iter().any(|id| id == property_id) {
            Origin::Recovered
        } else {
            Origin::Submitted
        }
    }

    /// The properties nothing more needs to be done about.
    #[must_use]
    pub fn cached_ids(&self) -> Vec<&str> {
        self.settled(true)
    }

    /// The properties still wanting a proof.
    #[must_use]
    pub fn work_ids(&self) -> Vec<&str> {
        self.settled(false)
    }

    fn settled(&self, done: bool) -> Vec<&str> {
        self.specs
            .iter()
            .filter(|spec| self.verified.contains_key(&spec.id) == done)
            .map(|spec| spec.id.as_str())
            .collect()
    }

    /// Whether there is nothing left to prove and nothing left to rewrite.
    #[must_use]
    pub fn complete(&self) -> bool {
        self.work_ids().is_empty() && self.stale.is_empty()
    }

    /// Check submitted proofs, caching what Lean accepts.
    ///
    /// Ids already verified are skipped rather than re-checked — resubmitting the
    /// whole set after a partial failure is the natural thing for a caller to do,
    /// and it should not cost another Mathlib import per settled property.
    ///
    /// # Errors
    ///
    /// [`UnknownProperty`] naming every id the session never registered. Nothing
    /// is checked when one is present: a caller that has the wrong session or the
    /// wrong ids should learn that before paying for Lean.
    pub fn check<V: Verifier>(
        &mut self,
        checker: &Checker<'_, V>,
        cache: &ProofCache,
        proofs: &[(String, String)],
    ) -> Result<Vec<Outcome>, UnknownProperty> {
        let mut unknown: Vec<String> = proofs
            .iter()
            .filter(|(id, _)| !self.registered(id))
            .map(|(id, _)| id.clone())
            .collect();
        unknown.sort();
        unknown.dedup();
        if !unknown.is_empty() {
            return Err(UnknownProperty { ids: unknown });
        }

        let submissions: Vec<Submission> = proofs
            .iter()
            .filter(|(id, _)| !self.verified.contains_key(id))
            .map(|(id, lean)| Submission::new(id, lean))
            .collect();
        for submission in &submissions {
            *self.attempts.entry(submission.id.clone()).or_default() += 1;
        }
        if submissions.is_empty() {
            return Ok(Vec::new());
        }

        let outcomes: Vec<Outcome> = match &self.lean_spec {
            Some(spec) => submissions
                .iter()
                .flat_map(|submission| checker.check_against(spec, submission, None))
                .collect(),
            None => checker.check_batch(&submissions, None),
        };
        for outcome in &outcomes {
            if !outcome.verified() {
                continue;
            }
            self.verified
                .insert(outcome.id.clone(), outcome.lean_code.clone());
            if outcome.recovered && !self.recovered.contains(&outcome.id) {
                self.recovered.push(outcome.id.clone());
            }
            if can_cache(outcome) {
                self.remember(cache, outcome);
            } else {
                log(
                    Tag::Cache,
                    &format!(
                        "{} verified but not cached — no evidence Lean accepted this proof",
                        outcome.id
                    ),
                );
            }
        }
        Ok(outcomes)
    }

    /// Compare the code's answers, by function, with the spec's answers.
    ///
    /// # Errors
    ///
    /// [`CompareError`] when the session compares no such function, or when the
    /// code gave a different number of answers than the spec has inputs.
    pub fn compare(
        &self,
        answers: &[(String, Vec<serde_json::Value>)],
    ) -> Result<Comparison, CompareError> {
        let mut paired = Vec::new();
        let mut unknown = Vec::new();
        for (function, code) in answers {
            match self
                .evaluated
                .iter()
                .find(|spec| spec.function == *function)
            {
                Some(spec) => paired.push((spec, code)),
                None => unknown.push(function.clone()),
            }
        }
        if !unknown.is_empty() {
            return Err(CompareError::Unknown(unknown));
        }
        let mut comparison = Comparison::default();
        for (spec, code) in paired {
            if code.len() != spec.inputs.len() {
                return Err(CompareError::Count {
                    function: spec.function.clone(),
                    answers: code.len(),
                    inputs: spec.inputs.len(),
                });
            }
            match spec.first_difference(code) {
                Some(difference) => comparison.differed.push(difference),
                None => comparison.matched.push(spec.function.clone()),
            }
        }
        Ok(comparison)
    }

    fn remember(&self, cache: &ProofCache, outcome: &Outcome) {
        let (Some(spec), Some(key)) = (self.spec(&outcome.id), self.keys.get(&outcome.id)) else {
            return;
        };
        cache.save(
            key,
            &PropertyResult {
                property_id: spec.id.clone(),
                description: spec.description.clone(),
                kind: spec.kind.clone(),
                function: spec.function.clone(),
                verified: true,
                lean_code: outcome.lean_code.clone(),
                lean_output: String::new(),
                retries: self
                    .attempts
                    .get(&outcome.id)
                    .copied()
                    .unwrap_or(1)
                    .saturating_sub(1),
                status: "verified".to_string(),
                fidelity: "unchecked".to_string(),
                preconditions: spec.preconditions.clone(),
                assumptions: spec.assumptions.clone(),
                ..PropertyResult::default()
            },
        );
    }
}

#[derive(serde::Deserialize, serde::Serialize)]
struct Searched {
    refutation: Option<Refutation>,
}

/// The properties of `spec` that have a counterexample, from the cache or from Lean.
///
/// The search only advises: a property it cannot test, or a Lean that never
/// ran, refutes nothing, and only a search Lean answered is cached.
pub fn search<V: Verifier>(verifier: &V, cache: &ProofCache, spec: &LeanSpec) -> Vec<Refutation> {
    let mut found: Vec<Option<Searched>> = spec
        .properties
        .iter()
        .map(|id| cache.load(&spec.search_key(id)))
        .collect();
    let missing: Vec<&str> = spec
        .properties
        .iter()
        .zip(&found)
        .filter(|(_, found)| found.is_none())
        .map(|(id, _)| id.as_str())
        .collect();
    if !missing.is_empty() {
        let search = spec.search(&missing);
        let said = verifier.verify(&search.lean_code, None).said();
        let mut read = read_search(&search, &said).into_iter();
        let unsearched = spec
            .properties
            .iter()
            .zip(&mut found)
            .filter(|(_, slot)| slot.is_none());
        for (id, slot) in unsearched {
            let refutation = match read.next() {
                Some(Answer::Refuted(refutation)) => Some(refutation),
                Some(Answer::Unrefuted) => None,
                Some(Answer::Silent) | None => continue,
            };
            let searched = Searched { refutation };
            cache.save(&spec.search_key(id), &searched);
            *slot = Some(searched);
        }
    }
    found
        .into_iter()
        .filter_map(|found| found?.refutation)
        .collect()
}

/// The inputs of each function `spec` compares, and the spec's answer to each.
///
/// The cache answers for a spec text it has seen; Lean evaluates the rest, in
/// one run.
///
/// # Errors
///
/// [`CompareError::Evaluation`] when Lean did not print the answers, and
/// [`CompareError::Unrun`] when formal could not run Lean.
pub fn evaluate<V: Verifier>(
    verifier: &V,
    cache: &ProofCache,
    spec: &LeanSpec,
) -> Result<Vec<Evaluated>, CompareError> {
    let found: Vec<Option<Evaluated>> = spec
        .compared
        .iter()
        .map(|compared| cache.load(&spec.answers_key(&compared.function)))
        .collect();
    let missing: Vec<&Compared> = spec
        .compared
        .iter()
        .zip(&found)
        .filter(|(_, found)| found.is_none())
        .map(|(compared, _)| compared)
        .collect();
    if missing.is_empty() {
        return Ok(found.into_iter().flatten().collect());
    }
    let functions: Vec<&str> = missing
        .iter()
        .map(|compared| compared.function.as_str())
        .collect();
    let result = verifier.verify(&spec.evaluation(&functions), None);
    if !result.success {
        return Err(result.first_error().map_or_else(
            || CompareError::Unrun(result.output.clone()),
            |error| CompareError::Evaluation(error.data.clone()),
        ));
    }
    let printed = result.printed();
    let printed: Vec<&str> = printed.iter().map(String::as_str).collect();
    let read = read_evaluation(&missing, &printed).map_err(CompareError::Evaluation)?;
    for evaluated in &read {
        cache.save(&spec.answers_key(&evaluated.function), evaluated);
    }
    let mut read = read.into_iter();
    Ok(found
        .into_iter()
        .filter_map(|found| found.or_else(|| read.next()))
        .collect())
}

/// The open sessions.
///
/// The lock covers the registry only — never a Lean run, which is slow and
/// belongs to exactly one session anyway. That is why a session comes back
/// wrapped rather than copied: the caller holds it for as long as its own check
/// takes, and nobody else waits on the registry meanwhile.
#[derive(Debug)]
pub struct Sessions {
    ttl: Duration,
    open: Mutex<HashMap<String, Arc<Mutex<Session>>>>,
}

impl Sessions {
    /// A registry whose sessions expire after `ttl`.
    #[must_use]
    pub fn new(ttl: Duration) -> Self {
        Self {
            ttl: ttl.max(MINIMUM_TTL),
            open: Mutex::new(HashMap::new()),
        }
    }

    /// The registry this process would use, `SESSION_TTL_MINUTES` included.
    #[must_use]
    pub fn from_env() -> Self {
        Self::resolve(&Env::process())
    }

    /// The same, from configuration that was collected rather than read.
    #[must_use]
    pub fn resolve(env: &Env) -> Self {
        Self::new(
            env.number("SESSION_TTL_MINUTES")
                .map_or(DEFAULT_TTL, Duration::from_mins),
        )
    }

    /// How long an idle session lasts.
    #[must_use]
    pub fn ttl(&self) -> Duration {
        self.ttl
    }

    /// Open a session, settling whatever the proof cache already knows.
    ///
    /// `stale` names properties whose source has changed since they were written
    /// down. They are reported rather than registered: proving a property against
    /// code it no longer describes produces a true theorem about nothing.
    pub fn open(
        &self,
        cache: &ProofCache,
        specs: Vec<PropertySpec>,
        stale: Vec<String>,
    ) -> Arc<Mutex<Session>> {
        self.open_as(Uuid::new_v4().simple().to_string(), cache, specs, stale)
    }

    /// Open a session on a Lean spec, with one property per `def … : Prop` in it.
    ///
    /// Lean evaluates the inputs of each function the spec compares, and
    /// searches each property for a counterexample, unless the cache already
    /// holds the answer.
    ///
    /// # Errors
    ///
    /// [`CompareError::Evaluation`] when Lean did not print the spec's answers, and
    /// [`CompareError::Unrun`] when formal could not run Lean.
    pub fn open_spec<V: Verifier>(
        &self,
        verifier: &V,
        cache: &ProofCache,
        spec: LeanSpec,
    ) -> Result<Arc<Mutex<Session>>, CompareError> {
        let evaluated = evaluate(verifier, cache, &spec)?;
        let refuted = search(verifier, cache, &spec);
        let keys = spec
            .properties
            .iter()
            .map(|id| (id.clone(), spec.key(id)))
            .collect();
        Ok(self.register(
            Uuid::new_v4().simple().to_string(),
            cache,
            spec.property_specs(),
            keys,
            Vec::new(),
            Some((spec, evaluated, refuted)),
        ))
    }

    /// The same, under an id chosen by the caller rather than generated.
    pub fn open_as(
        &self,
        id: String,
        cache: &ProofCache,
        specs: Vec<PropertySpec>,
        stale: Vec<String>,
    ) -> Arc<Mutex<Session>> {
        let keys = specs
            .iter()
            .map(|spec| (spec.id.clone(), spec.cache_key()))
            .collect();
        self.register(id, cache, specs, keys, stale, None)
    }

    fn register(
        &self,
        id: String,
        cache: &ProofCache,
        specs: Vec<PropertySpec>,
        keys: HashMap<String, String>,
        stale: Vec<String>,
        spec: Option<(LeanSpec, Vec<Evaluated>, Vec<Refutation>)>,
    ) -> Arc<Mutex<Session>> {
        self.evict_expired();
        let (lean_spec, evaluated, refuted) = spec.map_or(
            (None, Vec::new(), Vec::new()),
            |(spec, evaluated, refuted)| (Some(spec), evaluated, refuted),
        );

        let mut session = Session {
            id,
            created_at: Instant::now(),
            keys,
            specs,
            verified: HashMap::new(),
            attempts: HashMap::new(),
            hits: HashMap::new(),
            stale,
            recovered: Vec::new(),
            lean_spec,
            evaluated,
            refuted,
        };

        for spec in session.specs.clone() {
            let Some(key) = session.keys.get(&spec.id) else {
                continue;
            };
            let Some(cached) = cache
                .load::<PropertyResult>(key)
                .filter(|cached| cached.verified)
            else {
                continue;
            };
            session.verified.insert(spec.id.clone(), cached.lean_code);
            session.hits.insert(
                spec.id.clone(),
                CacheHit {
                    id: spec.id.clone(),
                    description: cached.description,
                    kind: cached.kind,
                    assumptions: cached.assumptions,
                },
            );
            log(
                Tag::Cache,
                &format!("{} cache hit — no proof needed", spec.id),
            );
        }

        log(
            Tag::Session,
            &format!(
                "{} opened — {} cached, {} to prove",
                &session.id[..8.min(session.id.len())],
                session.cached_ids().len(),
                session.work_ids().len()
            ),
        );

        let id = session.id.clone();
        let handle = Arc::new(Mutex::new(session));
        self.registry().insert(id, Arc::clone(&handle));
        handle
    }

    /// The session under `id`, if it is still open.
    #[must_use]
    pub fn get(&self, id: &str) -> Option<Arc<Mutex<Session>>> {
        self.evict_expired();
        self.registry().get(id).map(Arc::clone)
    }

    /// Close a session, reporting whether there was one to close.
    pub fn close(&self, id: &str) -> bool {
        self.registry().remove(id).is_some()
    }

    /// How many sessions are open.
    #[must_use]
    pub fn len(&self) -> usize {
        self.registry().len()
    }

    /// Whether nothing is open.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn registry(&self) -> std::sync::MutexGuard<'_, HashMap<String, Arc<Mutex<Session>>>> {
        self.open
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    fn evict_expired(&self) {
        let ttl = self.ttl;
        self.registry().retain(|_, session| {
            session
                .lock()
                .is_ok_and(|session| session.created_at.elapsed() < ttl)
        });
    }
}

impl Default for Sessions {
    fn default() -> Self {
        Self::new(DEFAULT_TTL)
    }
}
