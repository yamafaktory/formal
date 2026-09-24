//! What a proof rests on, asked of Lean after everything else in the file.

use serde::Deserialize;

use crate::verifier::{
    LeanError,
    LeanResult,
    Pos,
};

const AUDIT_BODY: &str = r#"
  let env ← _root_.Lean.MonadEnv.getEnv
  let locals := env.constants.map₂
  let mut found : Array _root_.Lean.Json := #[]
  for (name, _) in locals.toList do
    let mut seen : _root_.Lean.NameSet := {}
    let mut todo : List _root_.Lean.Name := [name]
    let mut foreign : Array _root_.Lean.Name := #[]
    repeat
      match todo with
      | [] => break
      | used :: rest =>
        todo := rest
        unless seen.contains used do
          seen := seen.insert used
          match env.find? used with
          | some (.axiomInfo _) =>
            unless [`propext, `Classical.choice, `Quot.sound].contains used do
              foreign := foreign.push used
          | some info =>
            if locals.contains used then
              todo := info.getUsedConstantsAsSet.toList ++ todo
          | none => pure ()
    unless foreign.isEmpty do
      let line := match ← _root_.Lean.findDeclarationRanges? name with
        | some ranges => _root_.Lean.Json.num ranges.range.pos.line
        | none => _root_.Lean.Json.null
      found := found.push (_root_.Lean.Json.mkObj [("name", _root_.Lean.Json.str name.toString), ("line", line), ("axioms", _root_.Lean.Json.arr (foreign.map fun ax => _root_.Lean.Json.str ax.toString))])
  _root_.Lean.logInfo m!"formal-audit {NONCE} {(_root_.Lean.Json.arr found).compress}"
"#;

/// A command that runs the audit, defined once in a Lean kept warm so that each
/// check calls it rather than compiling it again.
#[must_use]
pub fn definition() -> String {
    format!(
        "elab \"#formal_audit \" nonce:str : command => do{}",
        AUDIT_BODY.replace("NONCE", "nonce.getString")
    )
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
    text.replace("unexpected token 'run_cmd'", "unexpected end of input")
        .replace(
            "unexpected token '#formal_audit'",
            "unexpected end of input",
        )
}

fn with_newline(lean_code: &str) -> String {
    if lean_code.ends_with('\n') {
        lean_code.to_string()
    } else {
        format!("{lean_code}\n")
    }
}

#[derive(Deserialize)]
struct Finding {
    name: String,
    line: Option<u32>,
    axioms: Vec<String>,
}

#[derive(Deserialize)]
struct Message {
    #[serde(default)]
    severity: String,
    #[serde(default)]
    data: String,
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

    /// `lean_code` with the audit after it.
    #[must_use]
    pub fn appended_to(&self, lean_code: &str) -> String {
        format!(
            "{}\nrun_cmd do{}",
            with_newline(lean_code),
            AUDIT_BODY.replace("NONCE", &format!("\"{}\"", self.nonce))
        )
    }

    /// `lean_code` followed by a call to the audit [`definition`] made.
    #[must_use]
    pub fn called_after(&self, lean_code: &str) -> String {
        format!(
            "{}\n#formal_audit \"{}\"\n",
            with_newline(lean_code),
            self.nonce
        )
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
        let mut kept = Vec::new();
        for line in result.output.lines() {
            match serde_json::from_str::<Message>(line) {
                Ok(message)
                    if message.severity == "information" && message.data.starts_with(&marker) =>
                {
                    report = Some(message.data[marker.len()..].to_string());
                }
                _ => kept.push(line),
            }
        }
        result.output = kept.join("\n");

        let findings = report.and_then(|report| serde_json::from_str::<Vec<Finding>>(&report).ok());
        let Some(findings) = findings else {
            result.success = false;
            result.errors.push(LeanError {
                severity: "error".to_string(),
                data: UNAUDITED.to_string(),
                ..LeanError::default()
            });
            return result;
        };
        for finding in findings {
            result.success = false;
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
                pos: finding.line.map(|line| Pos {
                    line: Some(line),
                    column: Some(0),
                }),
                ..LeanError::default()
            });
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
    fn the_audit_follows_the_proof_on_a_line_of_its_own() {
        let code = audit().appended_to("theorem t : True := trivial");
        assert!(code.starts_with("theorem t : True := trivial\n\nrun_cmd do"));
        assert!(code.contains(r#"m!"formal-audit {"n0nce"} "#));
        assert!(!code.contains("NONCE"));
    }

    #[test]
    fn a_warm_check_calls_the_audit_it_was_given() {
        assert_eq!(
            audit().called_after("theorem t : True := trivial"),
            "theorem t : True := trivial\n\n#formal_audit \"n0nce\"\n"
        );
        let definition = definition();
        assert!(definition.starts_with("elab \"#formal_audit \" nonce:str : command => do\n"));
        assert!(definition.contains("{nonce.getString}"));
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
        for token in ["run_cmd", "#formal_audit"] {
            let mut result = clean(reported("[]"));
            result.success = false;
            result.errors.push(LeanError {
                severity: "error".to_string(),
                data: format!("unexpected token '{token}'; expected ')'"),
                ..LeanError::default()
            });
            let result = audit().judge(result);
            assert_eq!(
                result.errors[0].data,
                "unexpected end of input; expected ')'"
            );
        }
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
