//! The text formal serves, kept beside the code rather than inside it.
//!
//! Nothing here is executed: formal does not call a model. These files are the
//! accumulated guidance for the three judgements it cannot make for you, rendered
//! by [`crate::guide`] and reachable at `GET /guide/{topic}`.
//!
//! They live as files because they change on someone else's schedule. Lean
//! renames a diagnostic, Mathlib moves a lemma, and the fix is an edit to prose —
//! which should not mean touching code, and should read as a diff of what was
//! actually said.

macro_rules! guidance {
    ($($name:literal),* $(,)?) => {
        /// Every piece of guidance, by name, in the order the directory lists them.
        const GUIDANCE: &[(&str, &str)] = &[
            $(($name, include_str!(concat!("../guidance/", $name, ".md"))),)*
        ];
    };
}

guidance![
    "autoformalize_system",
    "decompose_system",
    "decompose_user",
    "filter_and_partition",
    "finite_case_analysis",
    "proof_generation_system",
    "proof_generation_user",
    "proof_retry_user",
    "property_extraction_system",
    "property_extraction_user",
    "property_formalize_and_prove_user",
    "search_before_proving",
    "statement_check",
];

/// The file holds the text plus one trailing newline, so it ends cleanly on disk.
///
/// That newline is removed rather than stripped: some guidance ends mid-sentence
/// and some ends with a blank line, and both must survive a round trip byte for
/// byte.
fn without_final_newline(text: &str) -> &str {
    text.strip_suffix('\n').unwrap_or(text)
}

/// One piece of guidance, as it is meant to be served.
///
/// Nothing, only for a name no file answers to. Every call site here passes a
/// literal that `include_str!` already proved exists at compile time.
#[must_use]
pub fn get(name: &str) -> Option<&'static str> {
    GUIDANCE
        .iter()
        .find(|(candidate, _)| *candidate == name)
        .map(|(_, text)| without_final_newline(text))
}

/// The same, empty rather than absent, for the call sites that cannot be wrong.
#[must_use]
pub fn text(name: &str) -> &'static str {
    get(name).unwrap_or_default()
}

/// Every piece of guidance on disk, by its upper-case name.
#[must_use]
pub fn names() -> Vec<String> {
    let mut names: Vec<String> = GUIDANCE
        .iter()
        .map(|(name, _)| name.to_uppercase())
        .collect();
    names.sort();
    names
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_name_in_the_table_resolves() {
        for (name, _) in GUIDANCE {
            assert!(get(name).is_some(), "{name}");
        }
        assert_eq!(names().len(), GUIDANCE.len());
    }

    #[test]
    fn a_name_nothing_answers_to_is_nothing() {
        assert_eq!(get("no_such_guidance"), None);
        assert_eq!(text("no_such_guidance"), "");
    }

    #[test]
    fn nothing_is_served_empty() {
        for (name, _) in GUIDANCE {
            assert!(!text(name).is_empty(), "{name}");
        }
    }

    #[test]
    fn exactly_one_newline_comes_off_the_end() {
        assert_eq!(without_final_newline("a\n\n"), "a\n");
        assert_eq!(without_final_newline("a\n"), "a");
        assert_eq!(without_final_newline("a"), "a");
    }

    #[test]
    fn nothing_served_ends_in_the_newline_the_file_ends_with() {
        for (name, _) in GUIDANCE {
            assert!(!text(name).ends_with("\n\n"), "{name}");
        }
    }

    #[test]
    fn the_names_are_the_upper_case_stems() {
        assert!(names().contains(&"DECOMPOSE_SYSTEM".to_string()));
    }
}
