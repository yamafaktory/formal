//! What the caller intends to prove, and what was established about it.
//!
//! Kept apart from whoever produced it. The proof cache persists a
//! [`PropertyResult`] and the session builds one, and neither should have to
//! import a pipeline to name the shape of its own result.

use serde::{
    Deserialize,
    Serialize,
};

use crate::proof_cache;

/// What the caller intends to prove about one function.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PropertySpec {
    /// Names the property across sessions, cache entries and proof files.
    pub id: String,
    /// Prose, and deliberately not part of the cache key.
    pub description: String,
    /// The category of claim — `invariant`, `bound`, `identity` and so on.
    pub kind: String,
    /// The name of the function the property is about.
    pub function: String,
    /// The source of that function, as it stood when the property was written.
    pub function_code: String,
    /// The claim itself, in the notation the guide describes.
    pub formal: String,
    /// What must hold of the inputs for the claim to be made at all.
    pub preconditions: Vec<String>,
    /// How the code was modelled in Lean, where the modelling is a choice.
    pub assumptions: Vec<String>,
}

impl PropertySpec {
    /// The cache entry this property would be found under.
    #[must_use]
    pub fn cache_key(&self) -> String {
        proof_cache::cache_key(&self.function_code, &self.kind, &self.formal)
    }
}

/// The record of what was established about one property.
///
/// This is the shape written into the proof cache, so its field names and their
/// order are the on-disk format. Renaming one orphans every entry that has it.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PropertyResult {
    /// The id of the property this settles.
    pub property_id: String,
    /// The description carried at the time the proof was accepted.
    pub description: String,
    /// The kind carried at the time the proof was accepted.
    pub kind: String,
    /// The name of the function the property is about.
    pub function: String,
    /// Whether Lean accepted the proof.
    pub verified: bool,
    /// The Lean that was accepted, or the last one attempted.
    pub lean_code: String,
    /// What Lean said, kept for a failure and empty for a cache entry.
    pub lean_output: String,
    /// Attempts before this one — zero when the first proof worked.
    pub retries: u32,
    /// Why a property is unverifiable or errored, when that needs saying.
    #[serde(default)]
    pub reason: String,
    /// `verified` | `failed` | `unverifiable` | `error`.
    #[serde(default = "PropertyResult::default_status")]
    pub status: String,
    /// `ok` | `diverges` | `unchecked`.
    #[serde(default = "PropertyResult::default_fidelity")]
    pub fidelity: String,
    /// The Lean statement read back into prose, when fidelity was checked.
    #[serde(default)]
    pub back_translation: String,
    /// Why fidelity was judged to diverge.
    #[serde(default)]
    pub fidelity_reason: String,
    /// What must hold of the inputs for the claim to be made at all.
    #[serde(default)]
    pub preconditions: Vec<String>,
    /// How the code was modelled in Lean, where the modelling is a choice.
    #[serde(default)]
    pub assumptions: Vec<String>,
    /// Whether this answer came from the cache rather than from a Lean run.
    #[serde(default)]
    pub cached: bool,
}

impl PropertyResult {
    fn default_status() -> String {
        "failed".to_string()
    }

    fn default_fidelity() -> String {
        "unchecked".to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn minimal() -> serde_json::Value {
        serde_json::json!({
            "property_id": "f/bound",
            "description": "the result is never empty",
            "kind": "bound",
            "function": "f",
            "verified": true,
            "lean_code": "theorem t : True := trivial",
            "lean_output": "",
            "retries": 0
        })
    }

    #[test]
    fn the_optional_fields_carry_the_defaults_python_gave_them() {
        let result: PropertyResult =
            serde_json::from_value(minimal()).expect("the minimal entry loads");
        assert_eq!(result.status, "failed");
        assert_eq!(result.fidelity, "unchecked");
        assert!(!result.cached);
        assert!(result.assumptions.is_empty());
    }

    #[test]
    fn a_missing_required_field_is_not_a_result() {
        let mut entry = minimal();
        entry.as_object_mut().expect("an object").remove("verified");
        assert!(serde_json::from_value::<PropertyResult>(entry).is_err());
    }

    #[test]
    fn an_entry_from_a_newer_formal_is_refused_rather_than_half_read() {
        let mut entry = minimal();
        entry
            .as_object_mut()
            .expect("an object")
            .insert("provenance".to_string(), serde_json::json!("elsewhere"));
        assert!(serde_json::from_value::<PropertyResult>(entry).is_err());
    }

    #[test]
    fn the_written_field_order_is_the_declared_one() {
        let text =
            serde_json::to_string_pretty(&PropertyResult::default()).expect("a result serialises");
        let first = text.lines().nth(1).expect("a first field");
        assert!(first.contains("property_id"), "{first}");
    }
}
