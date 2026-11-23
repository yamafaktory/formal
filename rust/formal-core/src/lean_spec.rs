//! A spec written in Lean, and the file formal checks a proof of it in.

use std::{
    collections::HashMap,
    fs,
    path::Path,
    sync::OnceLock,
};

use regex::Regex;

use crate::{
    lean_text::{
        Import,
        imports,
        runs_code,
        without_comments,
    },
    proof_cache::{
        lean_spec_answers_key,
        lean_spec_key,
    },
    property::PropertySpec,
    specs::{
        SpecError,
        expanduser,
        require_absolute,
    },
};

/// The command, defined before every proof, that requires `<id>.holds` to state `<id>`.
pub const HOLDS_COMMAND: &str = "#formal_holds";

/// What starts each line the evaluation prints, before the function and its answers.
pub const COMPARE_MARK: &str = "formal-compare";

const EVALUATION_IMPORT: &str = "Lean.Data.Json";

const ENCODING: &str = "namespace FormalCompare
scoped instance (priority := high) : Lean.ToJson Char := ⟨fun c => Lean.Json.str (String.singleton c)⟩
scoped instance (priority := high) : Lean.ToJson (List Char) := ⟨fun s => Lean.Json.str (String.ofList s)⟩
end FormalCompare";

/// A Lean file that defines the code's model and states its properties.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeanSpec {
    /// The spec as it was read, which is also what its cache keys digest.
    pub text: String,
    /// The namespace that holds the definitions and the properties.
    pub namespace: String,
    /// The id of each `def <name> : Prop`, as `<namespace>.<name>`, in the spec's order.
    pub properties: Vec<String>,
    /// The functions whose doc comment names the code they describe, in the spec's order.
    pub compared: Vec<Compared>,
}

/// A function of the spec that names the code it describes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Compared {
    /// The function, as `<namespace>.<name>`.
    pub function: String,
    /// What the `code:` line of its doc comment says.
    pub code: String,
}

/// The inputs of a compared function, and the spec's answer to each.
#[derive(Clone, Debug, PartialEq, serde::Deserialize, serde::Serialize)]
pub struct Evaluated {
    /// The function, as `<namespace>.<name>`.
    pub function: String,
    /// What the `code:` line of its doc comment says.
    pub code: String,
    /// The inputs, as JSON.
    pub inputs: Vec<serde_json::Value>,
    /// The spec's answer to each input, in the same order.
    pub answers: Vec<serde_json::Value>,
}

/// The first input on which the code and the spec disagree.
#[derive(Clone, Debug, PartialEq)]
pub struct Difference {
    /// The function, as `<namespace>.<name>`.
    pub function: String,
    /// The input.
    pub input: serde_json::Value,
    /// What the spec answers.
    pub spec: serde_json::Value,
    /// What the code answers.
    pub code: serde_json::Value,
}

impl Evaluated {
    /// The first input whose answer from the code is not the spec's answer.
    #[must_use]
    pub fn first_difference(&self, code: &[serde_json::Value]) -> Option<Difference> {
        self.inputs
            .iter()
            .zip(&self.answers)
            .zip(code)
            .find(|((_, spec), code)| spec != code)
            .map(|((input, spec), code)| Difference {
                function: self.function.clone(),
                input: input.clone(),
                spec: spec.clone(),
                code: code.clone(),
            })
    }
}

/// A proof put after the spec it proves, ready for Lean.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Composed {
    /// The file to check.
    pub lean_code: String,
    offset: u32,
    proof_lines: u32,
}

impl Composed {
    /// The line of the proof that a line of the composed file came from.
    #[must_use]
    pub fn proof_line(&self, line: u32) -> Option<u32> {
        line.checked_sub(self.offset)
            .filter(|&proof_line| proof_line >= 1 && proof_line <= self.proof_lines)
    }
}

const IDENTIFIER: &str = r"[\p{L}_][\p{L}\p{N}_'!?]*";

fn pattern(cell: &'static OnceLock<Regex>, source: impl FnOnce() -> String) -> &'static Regex {
    cell.get_or_init(|| Regex::new(&source()).expect("the pattern is built from literals"))
}

fn namespace_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"^\s*namespace\s+({IDENTIFIER}(?:\.{IDENTIFIER})*)\s*$")
    })
}

fn end_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"^\s*end\s+({IDENTIFIER}(?:\.{IDENTIFIER})*)\s*$")
    })
}

fn identifier_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || format!(r"^{IDENTIFIER}$"))
}

fn prop_definition_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        r"\b(def|abbrev)\s+([^\s:]+)\s*:\s*Prop\s*:=".to_string()
    })
}

const DEFINITION: &str =
    r"(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial)\s+)*(?:def|abbrev)\s+";

fn definition_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"(?m)^[ \t]*{DEFINITION}({IDENTIFIER}(?:\.{IDENTIFIER})*)")
    })
}

fn doc_comment_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || r"(?s)/--(.*?)-/".to_string())
}

fn documented_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"\A\s*{DEFINITION}({IDENTIFIER}(?:\.{IDENTIFIER})*)")
    })
}

fn code_line_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        r"(?m)^[ \t]*code:[ \t]*(\S[^\n]*?)[ \t]*$".to_string()
    })
}

fn compared_functions(
    path: &Path,
    text: &str,
    code: &str,
    namespace: &str,
    blocks: &[(String, usize, usize)],
) -> Result<Vec<Compared>, SpecError> {
    let defined: HashMap<&str, bool> = definition_pattern()
        .captures_iter(code)
        .filter_map(|found| {
            let at = found.get(0)?.start();
            let inside = blocks
                .iter()
                .any(|(_, start, end)| *start <= at && at < *end);
            Some((found.get(1)?.as_str(), inside))
        })
        .collect();
    let mut compared = Vec::new();
    for found in doc_comment_pattern().captures_iter(text) {
        let Some(code_line) = code_line_pattern().captures(&found[1]) else {
            continue;
        };
        let after = found.get(0).map_or("", |whole| &text[whole.end()..]);
        let name = documented_pattern()
            .captures(after)
            .and_then(|documented| documented.get(1))
            .map(|name| name.as_str());
        let name = match name.map(|name| (name, defined.get(name))) {
            Some((_, None)) => continue,
            Some((name, Some(true))) => name,
            _ => {
                return Err(SpecError::UncomparableCode {
                    path: path.to_path_buf(),
                    line: format!("code: {}", &code_line[1]),
                });
            }
        };
        let function = format!("{namespace}.{name}");
        if defined.get(format!("{name}.inputs").as_str()) != Some(&true) {
            return Err(SpecError::NoInputs {
                path: path.to_path_buf(),
                function,
            });
        }
        compared.push(Compared {
            function,
            code: code_line[1].to_string(),
        });
    }
    Ok(compared)
}

fn import_lines<'a>(modules: impl Iterator<Item = &'a str>) -> Vec<String> {
    let mut lines: Vec<String> = Vec::new();
    for module in modules {
        let line = format!("import {module}");
        if !lines.contains(&line) {
            lines.push(line);
        }
    }
    lines
}

fn evaluation_of(function: &str) -> String {
    format!(
        "open FormalCompare in\n#eval IO.println (\"{COMPARE_MARK} {function} \" ++ \
         (Lean.toJson ((_root_.{function}.inputs).map fun input => (input, _root_.{function} input))).compress)"
    )
}

fn blanked(code: &str, imports: &[Import]) -> String {
    let mut kept = String::with_capacity(code.len());
    let mut from = 0;
    for import in imports {
        kept.push_str(&code[from..import.start]);
        kept.extend(
            code[import.start..import.end]
                .chars()
                .map(|c| if c == '\n' { '\n' } else { ' ' }),
        );
        from = import.end;
    }
    kept.push_str(&code[from..]);
    kept
}

impl LeanSpec {
    /// Read the spec at an absolute path.
    ///
    /// # Errors
    ///
    /// [`SpecError`] when the path is relative or names nothing, or when the
    /// spec can run code, opens no namespace or more than one, states no
    /// property, or states one that formal cannot register.
    pub fn load(path: &str) -> Result<Self, SpecError> {
        let path = expanduser(path);
        require_absolute(&path, "spec")?;
        let text = fs::read_to_string(&path).map_err(|_| SpecError::NoSuchFile(path.clone()))?;
        Self::parse(&path, text)
    }

    fn parse(path: &Path, text: String) -> Result<Self, SpecError> {
        if let Some(found) = runs_code(&text) {
            return Err(SpecError::RunsCode {
                path: path.to_path_buf(),
                found,
            });
        }
        let code = without_comments(text.trim_start_matches('\u{feff}'));
        let mut namespaces: Vec<String> = Vec::new();
        let mut blocks: Vec<(String, usize, usize)> = Vec::new();
        let mut open: Option<(String, usize)> = None;
        let mut offset = 0;
        for line in code.split_inclusive('\n') {
            if let Some(found) = namespace_pattern().captures(line.trim_end()) {
                let namespace = found[1].to_string();
                if !namespaces.contains(&namespace) {
                    namespaces.push(namespace.clone());
                }
                open = Some((namespace, offset));
            } else if let Some(found) = end_pattern().captures(line.trim_end())
                && let Some((namespace, start)) = open.take_if(|(name, _)| *name == found[1])
            {
                blocks.push((namespace, start, offset));
            }
            offset += line.len();
        }
        if let Some((namespace, start)) = open {
            blocks.push((namespace, start, code.len()));
        }

        let mut properties = Vec::new();
        for found in prop_definition_pattern().captures_iter(&code) {
            let whole = found.get(0).map_or(0..0, |whole| whole.range());
            let line_start = code[..whole.start].rfind('\n').map_or(0, |index| index + 1);
            let block = blocks
                .iter()
                .find(|(_, start, end)| *start <= whole.start && whole.start < *end);
            let registrable = &found[1] == "def"
                && code[line_start..whole.start].trim().is_empty()
                && identifier_pattern().is_match(&found[2]);
            match block {
                Some((namespace, _, _)) if registrable => {
                    properties.push(format!("{namespace}.{}", &found[2]));
                }
                _ => {
                    let line_end = code[whole.end..]
                        .find('\n')
                        .map_or(code.len(), |index| whole.end + index);
                    return Err(SpecError::UnregisteredProperty {
                        path: path.to_path_buf(),
                        line: code[line_start..line_end]
                            .split_whitespace()
                            .collect::<Vec<_>>()
                            .join(" "),
                    });
                }
            }
        }
        let namespace = match namespaces.as_slice() {
            [] => return Err(SpecError::NoNamespace(path.to_path_buf())),
            [namespace] => namespace.clone(),
            _ => {
                return Err(SpecError::Namespaces {
                    path: path.to_path_buf(),
                    found: namespaces,
                });
            }
        };
        if properties.is_empty() {
            return Err(SpecError::NoLeanProperties(path.to_path_buf()));
        }
        let compared = compared_functions(path, &text, &code, &namespace, &blocks)?;
        Ok(Self {
            text,
            namespace,
            properties,
            compared,
        })
    }

    /// The properties as a session holds them.
    #[must_use]
    pub fn property_specs(&self) -> Vec<PropertySpec> {
        self.properties
            .iter()
            .map(|id| PropertySpec {
                id: id.clone(),
                kind: "spec".to_string(),
                ..PropertySpec::default()
            })
            .collect()
    }

    /// The cache key of a property, which covers the whole spec.
    #[must_use]
    pub fn key(&self, id: &str) -> String {
        lean_spec_key(&self.text, id)
    }

    /// The cache key of the spec's answers for a compared function.
    #[must_use]
    pub fn answers_key(&self, function: &str) -> String {
        lean_spec_answers_key(&self.text, ENCODING, &evaluation_of(function))
    }

    /// The file that prints the inputs of each function in `functions`, and the spec's answers.
    ///
    /// Each function prints one line: [`COMPARE_MARK`], the function, and a JSON
    /// list of `[input, answer]` pairs.
    #[must_use]
    pub fn evaluation(&self, functions: &[&str]) -> String {
        let spec = self.text.trim_start_matches('\u{feff}');
        let spec_imports = imports(spec);
        let mut lines = import_lines(
            std::iter::once(EVALUATION_IMPORT)
                .chain(spec_imports.iter().map(|import| import.module.as_str())),
        );
        lines.push(blanked(spec, &spec_imports));
        lines.push(ENCODING.to_string());
        lines.extend(functions.iter().map(|function| evaluation_of(function)));
        format!("{}\n", lines.join("\n"))
    }

    /// The file that checks `proof` against the property `id`.
    ///
    /// The imports of the spec and the proof come first, then the spec and a
    /// line that requires the spec to define `id`. The proof follows with its
    /// imports blanked, so that its lines keep their numbers. The last line
    /// calls a command defined before the proof, which requires `<id>.holds`
    /// to state the spec's own property.
    #[must_use]
    pub fn compose(&self, id: &str, proof: &str) -> Composed {
        let spec = self.text.trim_start_matches('\u{feff}');
        let proof = proof.trim_start_matches('\u{feff}');
        let spec_imports = imports(spec);
        let proof_imports = imports(proof);

        let mut lines = import_lines(
            spec_imports
                .iter()
                .chain(&proof_imports)
                .map(|import| import.module.as_str()),
        );
        lines.extend(blanked(spec, &spec_imports).split('\n').map(str::to_string));
        lines.push(format!("#check _root_.{id}"));
        let offset = u32::try_from(lines.len()).unwrap_or(u32::MAX);
        let body = blanked(proof, &proof_imports);
        lines.extend(body.split('\n').map(str::to_string));
        lines.push(format!("{HOLDS_COMMAND} \"{id}\""));
        Composed {
            lean_code: format!("{}\n", lines.join("\n")),
            offset,
            proof_lines: u32::try_from(body.split('\n').count()).unwrap_or(u32::MAX),
        }
    }
}

/// The answers the evaluation of `compared` printed, one per function.
///
/// # Errors
///
/// What is wrong, when a function printed no line, more than one, or a line
/// that is not a JSON list of `[input, answer]` pairs.
pub fn read_evaluation(compared: &[&Compared], printed: &[&str]) -> Result<Vec<Evaluated>, String> {
    compared
        .iter()
        .map(|Compared { function, code }| {
            let mark = format!("{COMPARE_MARK} {function} ");
            let lines: Vec<&str> = printed
                .iter()
                .filter_map(|line| line.strip_prefix(&mark))
                .collect();
            let [line] = lines.as_slice() else {
                return Err(format!(
                    "the evaluation printed {} answers for {function}, not one",
                    lines.len()
                ));
            };
            let pairs: Vec<(serde_json::Value, serde_json::Value)> =
                serde_json::from_str(line.trim_end()).map_err(|e| {
                    format!("the evaluation of {function} printed something else than pairs: {e}")
                })?;
            let (inputs, answers) = pairs.into_iter().unzip();
            Ok(Evaluated {
                function: function.clone(),
                code: code.clone(),
                inputs,
                answers,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::*;

    const DEMO: &str = include_str!("../../../tests/fixtures/lean_spec/Demo.lean");

    fn parse(text: &str) -> Result<LeanSpec, SpecError> {
        LeanSpec::parse(&PathBuf::from("/specs/Demo.lean"), text.to_string())
    }

    fn with(extra: &str) -> Result<LeanSpec, SpecError> {
        parse(&DEMO.replace("end Demo", &format!("{extra}\n\nend Demo")))
    }

    fn demo() -> LeanSpec {
        parse(DEMO).expect("the demo spec parses")
    }

    #[test]
    fn only_the_props_are_properties_and_they_keep_their_order() {
        assert_eq!(demo().properties, ["Demo.double_even", "Demo.double_mono"]);
    }

    #[test]
    fn a_property_may_be_indented_or_follow_its_doc_on_the_line() {
        let spec = with("  def indented : Prop := True\n/-- why -/ def documented : Prop := True")
            .expect("it parses");
        assert_eq!(
            spec.properties,
            [
                "Demo.double_even",
                "Demo.double_mono",
                "Demo.indented",
                "Demo.documented"
            ]
        );
    }

    #[test]
    fn a_name_takes_the_identifier_characters_of_lean() {
        let spec = parse(&DEMO.replace("double_mono", "double_mono'")).expect("it parses");
        assert_eq!(spec.properties, ["Demo.double_even", "Demo.double_mono'"]);
    }

    #[test]
    fn a_definition_whose_type_only_starts_with_prop_is_not_a_property() {
        let spec = with("def lift : Prop → Prop := id\ndef pair : Prop × Prop := (True, True)")
            .expect("it parses");
        assert_eq!(spec.properties, ["Demo.double_even", "Demo.double_mono"]);
    }

    #[test]
    fn a_property_in_a_comment_is_not_one() {
        let spec = with(
            "/-\ndef gone : Prop := True\nnamespace Model, below.\n-/\n-- def also_gone : Prop := True",
        )
        .expect("it parses");
        assert_eq!(spec.namespace, "Demo");
        assert_eq!(spec.properties, ["Demo.double_even", "Demo.double_mono"]);
    }

    #[test]
    fn a_property_formal_cannot_register_is_refused() {
        for written in [
            "@[simp] def tagged : Prop := True",
            "protected def guarded : Prop := True",
        ] {
            let refused = with(written);
            assert!(
                matches!(refused, Err(SpecError::UnregisteredProperty { .. })),
                "{written}: {refused:?}"
            );
        }
    }

    #[test]
    fn a_property_outside_the_namespace_is_refused() {
        let refused = parse(&format!(
            "{DEMO}\ndef outside : Prop := False\n\nnamespace Demo\n\ndef inside : Prop := True\n\nend Demo\n"
        ));
        assert!(
            matches!(refused, Err(SpecError::UnregisteredProperty { ref line, .. }) if line.contains("outside")),
            "{refused:?}"
        );
    }

    #[test]
    fn a_spec_with_two_namespaces_is_refused() {
        let refused = parse(&format!(
            "{DEMO}\nnamespace Other\ndef p : Prop := True\nend Other\n"
        ));
        assert!(
            matches!(refused, Err(SpecError::Namespaces { .. })),
            "{refused:?}"
        );
    }

    #[test]
    fn a_spec_that_runs_code_is_refused() {
        let refused = parse(&format!("{DEMO}\n#eval 1\n"));
        assert!(
            matches!(refused, Err(SpecError::RunsCode { .. })),
            "{refused:?}"
        );
    }

    #[test]
    fn a_spec_without_a_namespace_or_a_property_is_refused() {
        assert!(matches!(
            parse("def p : Prop := True\n"),
            Err(SpecError::UnregisteredProperty { .. })
        ));
        assert!(matches!(
            parse("def n : Nat := 1\n"),
            Err(SpecError::NoNamespace(_))
        ));
        assert!(matches!(
            parse("namespace E\ndef n : Nat := 1\nend E\n"),
            Err(SpecError::NoLeanProperties(_))
        ));
        assert!(matches!(
            LeanSpec::load("Relative.lean"),
            Err(SpecError::NotAbsolute { .. })
        ));
    }

    #[test]
    fn any_edit_to_the_spec_moves_every_key() {
        let original = demo();
        for edited in [
            DEMO.replace("n + n", "2 * n"),
            DEMO.replace("n + n", "n + n   "),
        ] {
            let edited = parse(&edited).expect("it parses");
            for id in &original.properties {
                assert_ne!(original.key(id), edited.key(id));
            }
        }
        assert_ne!(
            original.key("Demo.double_even"),
            original.key("Demo.double_mono")
        );
    }

    #[test]
    fn no_inline_property_shares_the_key_of_a_spec_property() {
        let spec = demo();
        let inline = PropertySpec {
            function_code: spec.text.clone(),
            kind: "spec".to_string(),
            formal: "Demo.double_even".to_string(),
            ..PropertySpec::default()
        };
        assert_ne!(inline.cache_key(), spec.key("Demo.double_even"));
    }

    #[test]
    fn the_composed_file_imports_once_and_keeps_the_proof_lines() {
        let proof = "/- Copyright\nimport Fake -/\nimport Mathlib\nimport Mathlib.Tactic\n\nnamespace Demo\ntheorem double_even.holds : double_even := by\n  omega\nend Demo";
        let composed = demo().compose("Demo.double_even", proof);
        let lines: Vec<&str> = composed.lean_code.split('\n').collect();
        assert_eq!(lines[..2], ["import Mathlib", "import Mathlib.Tactic"]);
        assert_eq!(
            lines
                .iter()
                .filter(|line| line.starts_with("import "))
                .count(),
            3
        );
        assert_eq!(
            lines
                .iter()
                .filter(|line| **line == "import Mathlib")
                .count(),
            1
        );
        let omega = lines
            .iter()
            .position(|line| *line == "  omega")
            .expect("the proof is in");
        assert_eq!(
            composed.proof_line(u32::try_from(omega + 1).expect("it fits")),
            Some(8)
        );
        assert!(
            composed
                .lean_code
                .contains("end Demo\n\n#check _root_.Demo.double_even\n/- Copyright")
        );
        assert!(
            composed
                .lean_code
                .ends_with("\n#formal_holds \"Demo.double_even\"\n")
        );
    }

    #[test]
    fn only_the_module_name_of_an_import_moves_before_the_spec() {
        let composed = demo().compose(
            "Demo.double_even",
            "/- c\n-/ import Mathlib /- open -/\nimport Mathlib.Tactic infixl:65 \" ++ \" => fun _ b => b\ntheorem t : True := trivial",
        );
        let spec_at = composed
            .lean_code
            .find("namespace Demo")
            .expect("the spec is in");
        assert_eq!(
            &composed.lean_code[..spec_at],
            "import Mathlib\nimport Mathlib.Tactic\n"
        );
        let body: Vec<&str> = composed.lean_code.split('\n').collect();
        assert!(body.contains(&format!("-/{}/- open -/", " ".repeat(16)).as_str()));
        assert!(
            body.contains(
                &format!("{}infixl:65 \" ++ \" => fun _ b => b", " ".repeat(22)).as_str()
            )
        );
    }

    #[test]
    fn a_byte_order_mark_does_not_hide_the_imports() {
        let composed = demo().compose(
            "Demo.double_even",
            "\u{feff}import Mathlib\ntheorem t : True := trivial",
        );
        assert!(
            composed
                .lean_code
                .starts_with("import Mathlib\nnamespace Demo")
        );
        let spec = parse(&format!("\u{feff}{DEMO}")).expect("it parses");
        assert_eq!(spec.namespace, "Demo");
    }

    #[test]
    fn a_property_may_break_across_lines_and_an_abbreviation_is_refused() {
        let spec =
            with("def split :\n  Prop := True\ndef late : Prop\n  := True").expect("it parses");
        assert_eq!(
            spec.properties,
            [
                "Demo.double_even",
                "Demo.double_mono",
                "Demo.split",
                "Demo.late"
            ]
        );
        let refused = with("abbrev shorthand : Prop := True");
        assert!(
            matches!(refused, Err(SpecError::UnregisteredProperty { .. })),
            "{refused:?}"
        );
    }

    const COMPARED: &str = "/-- Doubles.\n\n  code: src/double.rs double\n-/\ndef twice (n : Nat) : Nat := n + n\n\ndef twice.inputs : List Nat := [0, 1, 2]";

    #[test]
    fn a_code_line_in_a_doc_comment_names_the_code_of_a_function() {
        let spec = with(&format!(
            "{COMPARED}\n/-- code: src/half.rs half -/ def half (n : Nat) : Nat := n / 2\ndef half.inputs : List Nat := [4]"
        ))
        .expect("it parses");
        assert_eq!(
            spec.compared,
            [
                Compared {
                    function: "Demo.twice".to_string(),
                    code: "src/double.rs double".to_string(),
                },
                Compared {
                    function: "Demo.half".to_string(),
                    code: "src/half.rs half".to_string(),
                },
            ]
        );
        assert_eq!(demo().compared, []);
    }

    #[test]
    fn a_doc_comment_without_a_code_line_or_on_a_dead_definition_compares_nothing() {
        let spec = with(
            "/-- What double does. -/\ndef plain (n : Nat) : Nat := n\n/-\n/-- code: src/gone.rs gone -/\ndef gone (n : Nat) : Nat := n\n-/",
        )
        .expect("it parses");
        assert_eq!(spec.compared, []);
    }

    #[test]
    fn a_code_line_names_only_the_function_its_doc_comment_sits_on() {
        let spec = with(
            "/-- code: src/a.rs a -/\n@[simp] def a (n : Nat) : Nat := n\ndef a.inputs : List Nat := [0]\n/-- Helper. -/\ndef b (n : Nat) : Nat := n",
        )
        .expect("it parses");
        assert_eq!(
            spec.compared,
            [Compared {
                function: "Demo.a".to_string(),
                code: "src/a.rs a".to_string(),
            }]
        );
    }

    #[test]
    fn a_code_line_on_a_dotted_function_names_that_function() {
        let spec = with(
            "def f (n : Nat) : Nat := n\n/-- code: src/f.rs go -/\ndef f.go (n : Nat) : Nat := n\ndef f.go.inputs : List Nat := [0]",
        )
        .expect("it parses");
        assert_eq!(
            spec.compared,
            [Compared {
                function: "Demo.f.go".to_string(),
                code: "src/f.rs go".to_string(),
            }]
        );
    }

    #[test]
    fn a_compared_function_and_its_inputs_may_carry_attributes_and_modifiers() {
        let spec = with(
            "/-- code: src/f.rs f -/\npartial def f (n : Nat) : Nat := n\n@[reducible] abbrev f.inputs : List Nat := [0]",
        )
        .expect("it parses");
        assert_eq!(
            spec.compared,
            [Compared {
                function: "Demo.f".to_string(),
                code: "src/f.rs f".to_string(),
            }]
        );
    }

    #[test]
    fn a_code_line_on_no_function_of_the_namespace_is_refused() {
        let loose = with("/-- code: src/x.rs x -/\ntheorem x : True := trivial");
        assert!(
            matches!(loose, Err(SpecError::UncomparableCode { ref line, .. }) if line == "code: src/x.rs x"),
            "{loose:?}"
        );
        let outside = parse(&format!(
            "/-- code: src/f.rs f -/\ndef f (n : Nat) : Nat := n\ndef f.inputs : List Nat := [0]\n{DEMO}"
        ));
        assert!(
            matches!(outside, Err(SpecError::UncomparableCode { ref line, .. }) if line == "code: src/f.rs f"),
            "{outside:?}"
        );
    }

    #[test]
    fn a_function_that_names_its_code_without_inputs_is_refused() {
        let refused = with(&COMPARED.replace("def twice.inputs", "def twice_inputs"));
        assert!(
            matches!(refused, Err(SpecError::NoInputs { ref function, .. }) if function == "Demo.twice"),
            "{refused:?}"
        );
    }

    #[test]
    fn the_evaluation_prints_each_function_after_the_spec() {
        let spec = with(COMPARED).expect("it parses");
        let evaluation = spec.evaluation(&["Demo.twice"]);
        assert!(evaluation.starts_with("import Lean.Data.Json\nnamespace Demo"));
        assert!(evaluation.contains("end FormalCompare\nopen FormalCompare in\n#eval"));
        assert!(evaluation.ends_with(
            "(Lean.toJson ((_root_.Demo.twice.inputs).map fun input => (input, _root_.Demo.twice input))).compress)\n"
        ));
    }

    fn twice() -> Compared {
        Compared {
            function: "Demo.twice".to_string(),
            code: "src/double.rs double".to_string(),
        }
    }

    #[test]
    fn the_evaluation_is_read_back_as_inputs_and_answers() {
        let read = read_evaluation(
            &[&twice()],
            &[
                "formal-audit 1 []",
                "formal-compare Demo.twice [[0,0],[1,2]]\n",
            ],
        )
        .expect("it reads");
        assert_eq!(
            read,
            [Evaluated {
                function: "Demo.twice".to_string(),
                code: "src/double.rs double".to_string(),
                inputs: vec![0.into(), 1.into()],
                answers: vec![0.into(), 2.into()],
            }]
        );
    }

    #[test]
    fn the_first_input_where_the_answers_part_is_the_difference() {
        let evaluated = Evaluated {
            function: "Demo.twice".to_string(),
            code: "src/double.rs double".to_string(),
            inputs: vec![0.into(), 1.into(), 2.into()],
            answers: vec![0.into(), 2.into(), 4.into()],
        };
        assert_eq!(
            evaluated.first_difference(&[0.into(), 2.into(), 4.into()]),
            None
        );
        assert_eq!(
            evaluated.first_difference(&[0.into(), 3.into(), 5.into()]),
            Some(Difference {
                function: "Demo.twice".to_string(),
                input: 1.into(),
                spec: 2.into(),
                code: 3.into(),
            })
        );
        assert!(
            evaluated
                .first_difference(&[0.into(), "2".into(), 4.into()])
                .is_some()
        );
    }

    #[test]
    fn an_evaluation_that_printed_no_line_two_or_no_pairs_is_refused() {
        for printed in [
            vec![],
            vec![
                "formal-compare Demo.twice []",
                "formal-compare Demo.twice []",
            ],
            vec!["formal-compare Demo.twice [1, 2]"],
        ] {
            assert!(
                read_evaluation(&[&twice()], &printed).is_err(),
                "{printed:?}"
            );
        }
    }

    #[test]
    fn the_answers_key_is_not_the_key_of_a_property_of_the_same_name() {
        let spec = demo();
        assert_ne!(
            spec.answers_key("Demo.double_even"),
            spec.key("Demo.double_even")
        );
        assert_ne!(
            spec.answers_key("Demo.double"),
            parse(&DEMO.replace("n + n", "2 * n"))
                .expect("it parses")
                .answers_key("Demo.double")
        );
    }

    #[test]
    fn a_line_outside_the_proof_maps_to_nothing() {
        let composed = demo().compose("Demo.double_even", "theorem t : True := trivial");
        assert_eq!(composed.proof_line(1), None);
        assert_eq!(composed.proof_line(composed.offset), None);
        assert_eq!(composed.proof_line(composed.offset + 1), Some(1));
        assert_eq!(composed.proof_line(composed.offset + 2), None);
    }
}
