//! Identification of what is being proved.
//!
//! The key is a SHA-256 hash of:
//!   - pure function source code, trailing whitespace removed
//!   - the property kind
//!   - the formal statement, with operator spelling and spacing normalised
//!
//! Prose — the description, preconditions and assumptions — is deliberately not
//! in the key. See [`cache_key`] for why.

use std::sync::OnceLock;

use regex::{
    Captures,
    Regex,
};
use sha2::{
    Digest,
    Sha256,
};

use crate::pystr;

/// Canonical form is the symbol, not the word. Words were the wrong direction:
/// with whitespace stripped, `∀x` became `forallx`, which is also what the
/// identifier `forallx` becomes. The symbols cannot occur inside an identifier,
/// so they can. Longest first — `<->` contains `->`.
const ASCII_OPERATORS: &[(&str, &str)] = &[
    ("<->", "↔"),
    ("->", "→"),
    ("/\\", "∧"),
    ("\\/", "∨"),
    ("<>", "≠"),
    ("<=", "≤"),
    (">=", "≥"),
    ("⟶", "→"),
];

/// Spelled as words, so they only count on a word boundary: `in` inside `ainb`
/// is not the membership operator, and treating it as one merged unrelated
/// statements.
const WORD_OPERATORS: &[(&str, &str)] =
    &[("forall", "∀"), ("exists", "∃"), ("not", "¬"), ("in", "∈")];

fn word_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN.get_or_init(|| {
        let alternation = WORD_OPERATORS
            .iter()
            .map(|&(word, _)| word)
            .collect::<Vec<_>>()
            .join("|");
        Regex::new(&format!(r"\b({alternation})\b")).expect("the operator words are literals")
    })
}

/// Reduce a formal statement to the form two writers of it should agree on.
///
/// Operator spelling and spacing are free choices — `∀ x, p x → q x` and
/// `forall x, p x -> q x` are one statement — and an agent picks differently
/// from run to run where a fixed prompt at temperature 0 did not.
///
/// Word-spelled operators are matched on word boundaries, and only before the
/// whitespace goes. Replacing them afterwards, or by substring, merges
/// statements that merely contain the letters: `a∈b` and the unrelated `ainb`
/// both reduced to `ainb` under the previous version.
#[must_use]
pub fn normalise_formal(formal: &str) -> String {
    let mut formal = formal.to_string();
    for &(ascii_form, symbol) in ASCII_OPERATORS {
        formal = formal.replace(ascii_form, symbol);
    }
    let formal = word_pattern().replace_all(&formal, |caps: &Captures| {
        let word = &caps[1];
        WORD_OPERATORS
            .iter()
            .find(|&&(candidate, _)| candidate == word)
            .map_or_else(|| word.to_string(), |&(_, symbol)| symbol.to_string())
    });
    formal.chars().filter(|&c| !pystr::is_space(c)).collect()
}

/// Indentation is meaning in Python, so only trailing and surrounding space goes.
#[must_use]
pub fn normalise_code(function_code: &str) -> String {
    pystr::splitlines(pystr::strip(function_code))
        .into_iter()
        .map(pystr::rstrip)
        .collect::<Vec<_>>()
        .join("\n")
}

/// Join fields so that no field can imitate the boundary between two others.
///
/// Joining on a newline was ambiguous: normalised code and the kind may both
/// contain one, so `("X\na", "b", "c")` and `("X", "a\nb", "c")` produced the
/// same payload and therefore the same key — two distinct properties sharing
/// one cached proof. Length-prefixing each field removes the ambiguity whatever
/// the field contains.
///
/// The length is a count of characters, not of bytes. Normalisation puts
/// multi-byte operators into the statement, so the two differ for most real
/// inputs and a byte count moves every key.
fn framed(parts: &[&str]) -> String {
    let mut payload = String::new();
    for part in parts {
        payload.push_str(&part.chars().count().to_string());
        payload.push(':');
        payload.push_str(part);
    }
    payload
}

/// Identify a property by what is being proved, not by how it was described.
///
/// The description, preconditions and assumptions that used to be mixed in here
/// are English prose. A fixed prompt reproduces them verbatim, so the key worked
/// while formal wrote them itself; an agent paraphrases, and every paraphrase
/// was a fresh key and a re-proof. Across the 148 properties observed in a real
/// run, the function, its kind and the normalised formal statement separated all
/// of them — an observation about that corpus, not a theorem about the function.
/// Distinctness of digests would rest on sha256, which nothing here establishes.
///
/// The prompt hash is gone with them. What is cached is a proof Lean accepted,
/// and Lean's verdict does not depend on which prompt produced the theorem — and
/// a prompt change that alters the formalisation changes `formal`, which changes
/// the key anyway.
#[must_use]
pub fn cache_key(function_code: &str, kind: &str, formal: &str) -> String {
    let payload = framed(&[
        &normalise_code(function_code),
        &pystr::strip(kind).to_lowercase(),
        &normalise_formal(formal),
    ]);
    sha256_hex(&payload)
}

/// The cache key of one property of a Lean spec.
///
/// A key from [`cache_key`] digests a framed payload, which starts with a
/// digit. This payload starts with a word, so no inline property can claim the
/// key of a spec property. The spec is digested as written, since a space
/// inside a Lean string is meaning.
#[must_use]
pub fn lean_spec_key(spec: &str, id: &str) -> String {
    sha256_hex(&format!("lean-spec:{}", framed(&[spec, id])))
}

/// The cache key of the spec's answers to the inputs of one function.
///
/// It covers the encoding and the command that print the answers, so a change
/// to how formal prints them never serves answers printed the old way. Its own
/// word keeps it apart from the key of a property with the same name.
#[must_use]
pub fn lean_spec_answers_key(spec: &str, encoding: &str, command: &str) -> String {
    sha256_hex(&format!(
        "lean-spec-answers:{}",
        framed(&[spec, encoding, command])
    ))
}

/// The cache key of the search for a counterexample to one property.
///
/// It covers the helpers and the command that run the search, so a change to
/// either searches again.
#[must_use]
pub fn lean_spec_search_key(spec: &str, helpers: &str, command: &str) -> String {
    sha256_hex(&format!(
        "lean-spec-search:{}",
        framed(&[spec, helpers, command])
    ))
}

/// The SHA-256 digest of `text`, in lowercase hex.
#[must_use]
pub fn sha256_hex(text: &str) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    Sha256::digest(text.as_bytes())
        .iter()
        .flat_map(|byte| [byte >> 4, byte & 0xf])
        .map(|nibble| char::from(DIGITS[usize::from(nibble)]))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn iff_is_matched_before_the_arrow_inside_it() {
        assert_eq!(normalise_formal("a <-> b"), "a↔b");
    }

    #[test]
    fn a_word_operator_is_not_matched_inside_an_identifier() {
        assert_ne!(normalise_formal("a in b"), normalise_formal("ainb"));
        assert_eq!(normalise_formal("a in b"), "a∈b");
        assert_eq!(normalise_formal("ainb"), "ainb");
    }

    #[test]
    fn normalising_twice_changes_nothing() {
        let once = normalise_formal("forall x, p x -> q x");
        assert_eq!(normalise_formal(&once), once);
    }

    #[test]
    fn indentation_survives_but_trailing_space_does_not() {
        assert_eq!(
            normalise_code("\ndef f():\n    return 1   \n\n"),
            "def f():\n    return 1"
        );
    }

    #[test]
    fn no_field_can_imitate_the_boundary_of_another() {
        assert_ne!(cache_key("X\na", "b", "c"), cache_key("X", "a\nb", "c"));
    }

    #[test]
    fn the_kind_is_matched_case_insensitively() {
        assert_eq!(
            cache_key("f", "  Invariant  ", "p"),
            cache_key("f", "invariant", "p")
        );
    }

    #[test]
    fn a_word_operator_next_to_a_non_ascii_letter_is_part_of_a_word() {
        assert_eq!(normalise_formal("αin b"), "αinb");
        assert_eq!(normalise_formal("a inα"), "ainα");
    }

    #[test]
    fn the_kind_is_lowercased_with_unicode_rules() {
        assert_eq!(
            cache_key("f", "INVARIANTÉ", "p"),
            cache_key("f", "invarianté", "p")
        );
    }

    #[test]
    fn the_frame_counts_characters_and_not_bytes() {
        assert_eq!(framed(&["∀"]), "1:∀");
    }
}
