//! What a proof rests on, asked of Lean after everything else in the file.

use std::sync::OnceLock;

use formal_core::lean_text::without_comments;
use regex::Regex;
use serde::Deserialize;

use crate::verifier::{
    LeanError,
    LeanResult,
    Pos,
};

/// The source of the audit module.
pub const MODULE_SOURCE: &str = include_str!("../lean/FormalAudit.lean");

/// The name a file imports the audit module under.
pub const MODULE: &str = "FormalAudit";

const DISCARDED: &str = "formal-audit-discarded ";

/// A digest of the audit, so that a verdict can name the audit that gave it.
#[must_use]
pub fn module_digest() -> String {
    formal_core::proof_cache::sha256_hex(MODULE_SOURCE)
}

/// The axioms formal accepts a proof resting on.
pub const STANDARD_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

/// Why a check whose audit never reported is a failure.
pub const UNAUDITED: &str = "formal could not confirm that Lean checked the whole file: the axiom \
                             check formal appends after the proof never ran. `#exit`, an unclosed \
                             comment, or a trailing `... in` stops it.";

fn quoted<S: AsRef<str>>(names: &[S]) -> String {
    names
        .iter()
        .map(|name| format!("`{}`", name.as_ref()))
        .collect::<Vec<_>>()
        .join(", ")
}

fn as_if_unaudited(text: &str) -> String {
    text.replace(
        "unexpected token '#formal_audit'",
        "unexpected end of input",
    )
}

fn unaudited_error() -> LeanError {
    LeanError {
        severity: "error".to_string(),
        data: UNAUDITED.to_string(),
        ..LeanError::default()
    }
}

/// The verdict on a file whose audit could not have run.
#[must_use]
pub fn unaudited() -> LeanResult {
    LeanResult {
        success: false,
        output: UNAUDITED.to_string(),
        errors: vec![unaudited_error()],
    }
}

fn last_word_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    PATTERN.get_or_init(|| {
        Regex::new(r"(?:^|[^\p{L}\p{N}_'!?])(?:0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|[0-9][0-9_]*)?in$")
            .expect("the pattern is a literal")
    })
}

/// Whether `lean_code` ends in a `... in` that would take the next command as its own.
#[must_use]
pub fn leaves_an_in_open(lean_code: &str) -> bool {
    last_word_pattern().is_match(without_comments(lean_code).trim_end())
}

#[derive(Deserialize)]
struct Finding {
    name: String,
    line: Option<u32>,
    axioms: Vec<String>,
    #[serde(default)]
    kernel: Option<String>,
}

#[derive(Deserialize)]
struct Message {
    #[serde(default)]
    severity: String,
    #[serde(default)]
    data: String,
    #[serde(default)]
    pos: Option<Pos>,
}

/// One check's audit, told apart from anything the proof prints by a nonce the
/// proof cannot know.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Audit {
    nonce: String,
}

impl Default for Audit {
    fn default() -> Self {
        Self::new()
    }
}

impl Audit {
    /// An audit with a fresh nonce.
    #[must_use]
    pub fn new() -> Self {
        Self::with_nonce(uuid::Uuid::new_v4().simple().to_string())
    }

    /// An audit with a stated nonce.
    #[must_use]
    pub fn with_nonce(nonce: impl Into<String>) -> Self {
        Self {
            nonce: nonce.into(),
        }
    }

    fn marker(&self) -> String {
        format!("formal-audit {} ", self.nonce)
    }

    /// `lean_code` followed by a call to the audit.
    #[must_use]
    pub fn called_after(&self, lean_code: &str) -> String {
        let newline = if lean_code.ends_with('\n') { "" } else { "\n" };
        format!("{lean_code}{newline}\n#formal_audit \"{}\"\n", self.nonce)
    }

    /// The file a cold check gives Lean: the audit imported on a first line of
    /// its own, then `lean_code` and the call.
    #[must_use]
    pub fn cold_file(&self, lean_code: &str) -> String {
        format!(
            "import {MODULE}\n{}",
            self.called_after(lean_code.trim_start_matches('\u{feff}'))
        )
    }

    /// A cold result with each line moved back by the import formal put first.
    #[must_use]
    pub fn from_cold_file(result: LeanResult) -> LeanResult {
        result.map_lines(|line| line.checked_sub(1).filter(|&line| line > 0))
    }

    /// The verdict once the audit has been read: a failure when it never
    /// reported, or when a declaration rests on an axiom formal does not accept.
    #[must_use]
    pub fn judge(&self, mut result: LeanResult) -> LeanResult {
        for error in &mut result.errors {
            error.data = as_if_unaudited(&error.data);
        }
        result.output = as_if_unaudited(&result.output);
        let marker = self.marker();
        let mut report = None;
        let mut discarded: Vec<Finding> = Vec::new();
        let mut kept = Vec::new();
        for line in result.output.lines() {
            match serde_json::from_str::<Message>(line) {
                Ok(message)
                    if message.severity == "information" && message.data.starts_with(&marker) =>
                {
                    report = Some(message.data[marker.len()..].to_string());
                }
                Ok(message)
                    if message.severity == "information" && message.data.starts_with(DISCARDED) =>
                {
                    let at = message.pos.and_then(|pos| pos.line);
                    let found: Vec<Finding> =
                        serde_json::from_str(&message.data[DISCARDED.len()..]).unwrap_or_default();
                    discarded.extend(found.into_iter().map(|finding| Finding {
                        line: finding.line.or(at),
                        ..finding
                    }));
                }
                _ => kept.push(line),
            }
        }
        result.output = kept.join("\n");

        let findings = report.and_then(|report| serde_json::from_str::<Vec<Finding>>(&report).ok());
        let Some(mut findings) = findings else {
            result.success = false;
            result.errors.push(unaudited_error());
            return result;
        };
        findings.extend(discarded);
        for finding in findings {
            result.success = false;
            let pos = finding.line.map(|line| Pos {
                line: Some(line),
                column: Some(0),
            });
            if !finding.axioms.is_empty() {
                let what = if finding.axioms == [finding.name.clone()] {
                    format!("`{}` is an axiom", finding.name)
                } else {
                    format!("`{}` rests on {}", finding.name, quoted(&finding.axioms))
                };
                result.errors.push(LeanError {
                    severity: "error".to_string(),
                    data: format!(
                        "{what}, and formal accepts only {}. A proof that depends on another axiom, \
                         on `sorry` or on `native_decide` establishes nothing.",
                        quoted(&STANDARD_AXIOMS)
                    ),
                    pos: pos.clone(),
                    ..LeanError::default()
                });
            }
            if let Some(why) = finding.kernel {
                result.errors.push(LeanError {
                    severity: "error".to_string(),
                    data: format!(
                        "`{}` does not pass the kernel's check, so it was added without one: {why}",
                        finding.name
                    ),
                    pos,
                    ..LeanError::default()
                });
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn audit() -> Audit {
        Audit::with_nonce("n0nce")
    }

    fn reported(findings: &str) -> String {
        serde_json::json!({ "severity": "information", "data": format!("formal-audit n0nce {findings}") })
            .to_string()
    }

    fn clean(output: String) -> LeanResult {
        LeanResult {
            success: true,
            output,
            errors: Vec::new(),
        }
    }

    #[test]
    fn a_cold_file_imports_the_audit_first_and_calls_it_last() {
        assert_eq!(
            audit().cold_file("import Mathlib\n\ntheorem t : True := trivial"),
            "import FormalAudit\nimport Mathlib\n\ntheorem t : True := trivial\n\n#formal_audit \"n0nce\"\n"
        );
    }

    #[test]
    fn a_line_of_a_cold_file_is_read_back_as_a_line_of_the_proof() {
        let error = |line: u32| LeanError {
            pos: Some(Pos {
                line: Some(line),
                column: Some(2),
            }),
            ..LeanError::default()
        };
        let result = Audit::from_cold_file(LeanResult {
            errors: vec![error(5), error(1)],
            ..LeanResult::default()
        });
        let lines: Vec<(Option<u32>, Option<u32>)> =
            result.errors.iter().map(LeanError::position).collect();
        assert_eq!(lines, [(Some(4), Some(2)), (None, None)]);
    }

    #[test]
    fn only_a_last_word_in_leaves_the_audit_call_open() {
        for (code, open) in [
            (
                "theorem t : True := trivial\n\nset_option maxRecDepth 1 in",
                true,
            ),
            (
                "theorem t : True := trivial\nset_option maxRecDepth 1 in -- note\n",
                true,
            ),
            (
                "theorem t : True := trivial\nset_option maxRecDepth 512in",
                true,
            ),
            (
                "theorem t : True := trivial\nset_option «maxRecDepth» 1»in",
                true,
            ),
            ("theorem t : True := (trivial)in", true),
            (
                "theorem t : True := trivial\n-- set_option maxRecDepth 1 in",
                false,
            ),
            (
                "theorem t : True := by\n  exact (fun x => x) trivial\n-- in",
                false,
            ),
            ("def begin : Nat := 1", false),
            ("def x2in : Nat := 1\n#check x2in", false),
            (
                "theorem t : True := trivial\nset_option maxRecDepth 0x200in",
                true,
            ),
            (
                "theorem t : True := trivial\nset_option maxRecDepth 0b1in",
                true,
            ),
            (
                "theorem t : True := trivial\nset_option maxRecDepth 0o7in",
                true,
            ),
        ] {
            assert_eq!(leaves_an_in_open(code), open, "{code:?}");
        }
    }

    #[test]
    fn the_module_defines_the_command_formal_calls() {
        assert!(MODULE_SOURCE.contains("elab \"#formal_audit \" nonce:str : command"));
        assert_eq!(
            audit().called_after("theorem t : True := trivial"),
            "theorem t : True := trivial\n\n#formal_audit \"n0nce\"\n"
        );
    }

    #[test]
    fn a_byte_order_mark_does_not_follow_the_audit_import() {
        assert!(
            audit()
                .cold_file("\u{feff}import Mathlib\n")
                .starts_with("import FormalAudit\nimport Mathlib\n")
        );
    }

    #[test]
    fn the_module_defines_the_check_a_spec_composes_its_proofs_with() {
        assert!(MODULE_SOURCE.contains(&format!(
            "elab \"{} \" target:str : command",
            formal_core::lean_spec::HOLDS_COMMAND
        )));
    }

    #[test]
    fn the_module_accepts_the_axioms_the_message_names() {
        for axiom in STANDARD_AXIOMS {
            assert!(MODULE_SOURCE.contains(&format!("``{axiom}")), "{axiom}");
        }
    }

    #[test]
    fn a_declaration_lean_discarded_fails_at_the_line_that_reported_it() {
        let discarded = serde_json::json!({
            "severity": "information",
            "data": r#"formal-audit-discarded [{"name":"_example","line":null,"axioms":["sorryAx"]}]"#,
            "pos": { "line": 4, "column": 0 },
        });
        let result = audit().judge(clean(format!("{discarded}\n{}", reported("[]"))));
        assert!(!result.success);
        assert!(
            result.errors[0]
                .data
                .starts_with("`_example` rests on `sorryAx`"),
            "{}",
            result.errors[0].data
        );
        assert_eq!(result.errors[0].position(), (Some(4), Some(0)));
        assert_eq!(result.output, "");
    }

    #[test]
    fn two_audits_do_not_share_a_nonce() {
        assert_ne!(Audit::new(), Audit::new());
    }

    #[test]
    fn a_clean_report_leaves_the_verdict_and_leaves_the_output() {
        let result = audit().judge(clean(format!("before\n{}", reported("[]"))));
        assert!(result.success);
        assert_eq!(result.errors, []);
        assert_eq!(result.output, "before");
    }

    #[test]
    fn no_report_is_a_failure() {
        let result = audit().judge(clean(String::new()));
        assert!(!result.success);
        assert_eq!(result.errors[0].data, UNAUDITED);
        assert_eq!(result.errors[0].position(), (None, None));
    }

    #[test]
    fn a_report_under_another_nonce_is_not_the_audit() {
        let forged =
            serde_json::json!({ "severity": "information", "data": "formal-audit guess []" })
                .to_string();
        assert!(!audit().judge(clean(forged)).success);
    }

    #[test]
    fn a_report_that_is_not_information_is_not_the_audit() {
        let printed = serde_json::json!({ "severity": "warning", "data": "formal-audit n0nce []" })
            .to_string();
        assert!(!audit().judge(clean(printed)).success);
    }

    #[test]
    fn a_foreign_axiom_fails_the_declaration_where_it_was_made() {
        let result = audit().judge(clean(reported(
            r#"[{"name":"p0","line":3,"axioms":["cheat"]},{"name":"aux","line":null,"axioms":["sorryAx"]}]"#,
        )));
        assert!(!result.success);
        assert_eq!(result.errors.len(), 2);
        assert!(
            result.errors[0].data.starts_with("`p0` rests on `cheat`"),
            "{}",
            result.errors[0].data
        );
        assert_eq!(result.errors[0].position(), (Some(3), Some(0)));
        assert_eq!(result.errors[1].position(), (None, None));
    }

    #[test]
    fn a_declaration_the_kernel_rejects_fails_where_it_was_made() {
        let result = audit().judge(clean(reported(
            r#"[{"name":"s","line":4,"axioms":[],"kernel":"(kernel) type mismatch"}]"#,
        )));
        assert!(!result.success);
        assert_eq!(result.errors.len(), 1);
        assert!(
            result.errors[0]
                .data
                .starts_with("`s` does not pass the kernel's check"),
            "{}",
            result.errors[0].data
        );
        assert!(result.errors[0].data.ends_with("(kernel) type mismatch"));
        assert_eq!(result.errors[0].position(), (Some(4), Some(0)));
    }

    #[test]
    fn an_axiom_is_named_as_one() {
        let result = audit().judge(clean(reported(
            r#"[{"name":"cheat","line":2,"axioms":["cheat"]}]"#,
        )));
        assert!(
            result.errors[0]
                .data
                .starts_with("`cheat` is an axiom, and formal accepts only"),
            "{}",
            result.errors[0].data
        );
    }

    #[test]
    fn a_proof_cut_short_reads_as_it_did_before_the_audit() {
        let mut result = clean(reported("[]"));
        result.success = false;
        result.errors.push(LeanError {
            severity: "error".to_string(),
            data: "unexpected token '#formal_audit'; expected ')'".to_string(),
            ..LeanError::default()
        });
        let result = audit().judge(result);
        assert_eq!(
            result.errors[0].data,
            "unexpected end of input; expected ')'"
        );
    }

    #[test]
    fn the_audit_comes_after_what_lean_said() {
        let mut result = clean(reported(r#"[{"name":"h","line":2,"axioms":["sorryAx"]}]"#));
        result.success = false;
        result.errors.push(LeanError {
            severity: "error".to_string(),
            data: "declaration uses sorry".to_string(),
            ..LeanError::default()
        });
        let result = audit().judge(result);
        assert_eq!(result.errors[0].data, "declaration uses sorry");
    }
}
