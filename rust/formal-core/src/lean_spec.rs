//! A spec written in Lean, and the file formal checks a proof of it in.

use std::{
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
    proof_cache::lean_spec_key,
    property::PropertySpec,
    specs::{
        SpecError,
        expanduser,
        require_absolute,
    },
};

/// The command, defined before every proof, that requires `<id>.holds` to state `<id>`.
pub const HOLDS_COMMAND: &str = "#formal_holds";

/// A Lean file that defines the code's model and states its properties.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeanSpec {
    /// The spec as it was read, which is also what its cache keys digest.
    pub text: String,
    /// The namespace that holds the definitions and the properties.
    pub namespace: String,
    /// The id of each `def <name> : Prop`, as `<namespace>.<name>`, in the spec's order.
    pub properties: Vec<String>,
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
        Ok(Self {
            text,
            namespace,
            properties,
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

        let mut lines: Vec<String> = Vec::new();
        for import in spec_imports.iter().chain(&proof_imports) {
            let line = format!("import {}", import.module);
            if !lines.contains(&line) {
                lines.push(line);
            }
        }
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

    #[test]
    fn a_line_outside_the_proof_maps_to_nothing() {
        let composed = demo().compose("Demo.double_even", "theorem t : True := trivial");
        assert_eq!(composed.proof_line(1), None);
        assert_eq!(composed.proof_line(composed.offset), None);
        assert_eq!(composed.proof_line(composed.offset + 1), Some(1));
        assert_eq!(composed.proof_line(composed.offset + 2), None);
    }
}
