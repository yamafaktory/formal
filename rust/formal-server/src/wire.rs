//! What arrives and what goes back.
//!
//! Separate from the routing because these shapes are the contract: the golden
//! file pins every field name here, and a rename is a decision rather than a
//! refactor.

use formal_core::property::PropertySpec;
use formal_service::{
    checker::Outcome,
    session::{
        Comparison,
        Session,
    },
};
use indexmap::IndexMap;
use serde::{
    Deserialize,
    Serialize,
};
use utoipa::ToSchema;

/// One property, as a caller states it inline.
#[derive(Clone, Debug, Deserialize, ToSchema)]
pub struct PropertySpecIn {
    /// How a human reads the diff.
    pub id: String,
    /// One line of prose for a reviewer.
    pub description: String,
    /// The category of claim.
    #[serde(default)]
    pub kind: String,
    /// The function it is about.
    #[serde(default)]
    pub function: String,
    /// That function's source, as it stood when the property was written.
    #[serde(default)]
    pub function_code: String,
    /// The claim itself.
    #[serde(default)]
    pub formal: String,
    /// What must hold of the inputs.
    #[serde(default)]
    pub preconditions: Vec<String>,
    /// How the code is modelled in Lean.
    #[serde(default)]
    pub assumptions: Vec<String>,
}

impl PropertySpecIn {
    /// The same property, as the rest of formal holds it.
    #[must_use]
    pub fn into_spec(&self) -> PropertySpec {
        PropertySpec {
            id: self.id.clone(),
            description: self.description.clone(),
            kind: self.kind.clone(),
            function: self.function.clone(),
            function_code: self.function_code.clone(),
            formal: self.formal.clone(),
            preconditions: self.preconditions.clone(),
            assumptions: self.assumptions.clone(),
        }
    }
}

/// What to open a session over: properties inline, a spec file, or a Lean spec.
#[derive(Clone, Debug, Default, Deserialize, ToSchema)]
pub struct SessionRequest {
    /// The properties, stated inline.
    #[serde(default)]
    pub properties: Vec<PropertySpecIn>,
    /// An absolute path to a spec file instead.
    #[serde(default)]
    pub spec_file: Option<String>,
    /// An absolute path to a Lean spec instead, with one property per `def … : Prop`.
    #[serde(default)]
    pub spec: Option<String>,
    /// What each spec's `source_file` resolves against; the spec file's own
    /// directory by default.
    #[serde(default)]
    pub root: Option<String>,
}

/// What a cached proof established, so a caller can reject a mismatch.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct CacheHitOut {
    /// The property it settles.
    pub id: String,
    /// How it was described when it was proved.
    pub description: String,
    /// What kind of claim it was.
    pub kind: String,
    /// How the code was modelled in Lean.
    pub assumptions: Vec<String>,
}

/// Where a session stands.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct SessionResponse {
    /// What to name it in later requests.
    pub session_id: String,
    /// What the cache already settled.
    pub cached: Vec<CacheHitOut>,
    /// What still wants a proof.
    pub work: Vec<String>,
    /// Whether there is nothing left to do.
    pub complete: bool,
    /// Properties reported rather than proved, because their source moved.
    pub stale: Vec<String>,
    /// The functions of the Lean spec whose code to compare with the spec.
    pub compare: Vec<CompareOut>,
    /// The properties of the Lean spec the search found a counterexample to.
    pub refuted: Vec<RefutationOut>,
    /// The invariants that held in every state the bounded check reached.
    pub bounded: Vec<BoundOut>,
    /// The invariants a step can break from a state where they hold, so their proofs need stronger ones.
    pub not_inductive: Vec<NotInductiveOut>,
    /// Invariants that are not inductive one by one, and are kept by every step together.
    pub inductive_together: Vec<String>,
}

/// An invariant a step breaks from a state where it holds.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct NotInductiveOut {
    /// The property, as `<Namespace>.<name>.always`.
    pub id: String,
    /// The state where the invariant holds, as Lean prints it.
    pub state: String,
    /// The action, as Lean prints it.
    pub action: String,
    /// The state after the action, where the invariant does not hold.
    pub next: String,
}

/// An invariant that held in every state the bounded check reached.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct BoundOut {
    /// The property, as `<Namespace>.<name>.always`.
    pub id: String,
    /// How many actions deep the check explored.
    pub depth: u32,
    /// How many distinct states it reached.
    pub states: u32,
}

/// A property of the Lean spec, and the values for which it does not hold.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct RefutationOut {
    /// The property.
    pub id: String,
    /// The value of each variable, as Plausible prints it.
    pub counterexample: Vec<String>,
    /// What does not hold for those values.
    pub issue: String,
}

/// A function of the Lean spec, and the inputs its code must answer.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct CompareOut {
    /// The function, as `<namespace>.<name>`.
    pub function: String,
    /// What the `code:` line of its doc comment names.
    pub code: String,
    /// The inputs, as JSON, in the order the answers must follow.
    pub inputs: Vec<serde_json::Value>,
}

/// The code's answers to the inputs of each function, by function.
#[derive(Clone, Debug, Default, Deserialize, ToSchema)]
pub struct CompareRequest {
    /// The answers, as JSON, in the order of the inputs.
    #[serde(default)]
    pub answers: IndexMap<String, Vec<serde_json::Value>>,
}

/// The first input on which the code and the spec disagree.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct DifferenceOut {
    /// The function.
    pub function: String,
    /// The input.
    pub input: serde_json::Value,
    /// What the spec answers.
    pub spec: serde_json::Value,
    /// What the code answers.
    pub code: serde_json::Value,
}

/// What came of comparing the code's answers with the spec's.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct CompareResponse {
    /// The functions whose code answers what the spec answers on every input.
    pub matched: Vec<String>,
    /// The functions whose code differs, with the first input where it does.
    pub differed: Vec<DifferenceOut>,
}

impl From<Comparison> for CompareResponse {
    fn from(comparison: Comparison) -> Self {
        Self {
            matched: comparison.matched,
            differed: comparison
                .differed
                .into_iter()
                .map(|difference| DifferenceOut {
                    function: difference.function,
                    input: difference.input,
                    spec: difference.spec,
                    code: difference.code,
                })
                .collect(),
        }
    }
}

/// Proofs to check: inline, or as paths the server reads.
///
/// The maps keep the order they arrived in, so the first unreadable path is the
/// one reported rather than whichever sorted first.
#[derive(Clone, Debug, Default, Deserialize, ToSchema)]
pub struct CheckRequest {
    /// Lean, by property id.
    #[serde(default)]
    pub proofs: IndexMap<String, String>,
    /// Absolute paths to `.lean` files, read by the server.
    ///
    /// Every caller so far wrote a script to load these and escape them into
    /// `proofs`; this removes the need.
    #[serde(default)]
    pub proof_files: IndexMap<String, String>,
}

/// One rejected proof, and what to do about it.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct FailureOut {
    /// The property it was for.
    pub id: String,
    /// The first thing Lean objected to.
    pub error: String,
    /// Where, in the file that was submitted.
    pub line: Option<u32>,
    /// Which column.
    pub col: Option<u32>,
    /// The advice for that specific error.
    pub hint: String,
}

/// What came of a check.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct CheckResponse {
    /// The ids Lean accepted a proof of.
    pub verified: Vec<String>,
    /// Verified ids whose accepted proof is not the one that was sent.
    ///
    /// The recovery chain found another. Fetch it from
    /// `/session/{id}/proof/{property_id}`.
    pub recovered: Vec<String>,
    /// The ids that did not pass, with the reason each did not.
    pub failed: Vec<FailureOut>,
    /// What is still outstanding in the session as a whole.
    pub remaining: Vec<String>,
    /// Whether there is nothing left to do.
    pub complete: bool,
}

impl CheckResponse {
    /// The answer to one check, read off the outcomes and the session behind them.
    #[must_use]
    pub fn of(outcomes: &[Outcome], session: &Session) -> Self {
        Self {
            verified: outcomes
                .iter()
                .filter(|outcome| outcome.verified())
                .map(|outcome| outcome.id.clone())
                .collect(),
            recovered: outcomes
                .iter()
                .filter(|outcome| outcome.verified() && outcome.recovered)
                .map(|outcome| outcome.id.clone())
                .collect(),
            failed: outcomes
                .iter()
                .filter(|outcome| !outcome.verified())
                .map(|outcome| FailureOut {
                    id: outcome.id.clone(),
                    error: outcome.error.clone(),
                    line: outcome.line,
                    col: outcome.col,
                    hint: outcome.hint.clone(),
                })
                .collect(),
            remaining: session
                .work_ids()
                .into_iter()
                .map(ToString::to_string)
                .collect(),
            complete: session.complete(),
        }
    }
}

/// The proof Lean actually accepted, which is also the one that was cached.
#[derive(Clone, Debug, Serialize, ToSchema)]
pub struct ProofOut {
    /// The property it proves.
    pub id: String,
    /// `submitted`, `recovered` or `cache`.
    pub origin: String,
    /// The Lean itself.
    pub lean_code: String,
}
