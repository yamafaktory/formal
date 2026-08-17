//! Tests for checked-in property specs.
//!
//! Two independent extraction runs over one function agreed on the wording of
//! none of their properties, so specs derived fresh each run can never hit the
//! cache. Writing them down fixes that, and introduces the one risk worth testing
//! hardest: a spec outliving the code it describes.

use std::{
    fs,
    path::{
        Path,
        PathBuf,
    },
};

use formal_core::specs::{
    self,
    SPEC_VERSION,
    SpecError,
};
use serde_json::{
    Value,
    json,
};
use tempfile::TempDir;

const FUNCTION: &str = "def fmt_elapsed(seconds):\n    if seconds < 60:\n        return f\"{seconds:.1f}s\"\n    return \"long\"";

fn entry() -> Value {
    json!({
        "id": "fmt_elapsed/bound",
        "function": "fmt_elapsed",
        "kind": "bound",
        "formal": "forall x, 0 <= x -> fmt_elapsed x != []",
        "description": "the result is never empty",
        "assumptions": ["strings modelled as List Char"],
    })
}

fn with(overrides: &[(&str, Value)]) -> Value {
    let mut entry = entry();
    let object = entry.as_object_mut().expect("an object");
    for (name, value) in overrides {
        object.insert((*name).to_string(), value.clone());
    }
    entry
}

struct Workspace(TempDir);

impl Workspace {
    fn new() -> Self {
        Self(TempDir::new().expect("a temporary directory"))
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.path().join(name)
    }

    fn write(&self, name: &str, contents: &str) -> PathBuf {
        let path = self.path(name);
        fs::write(&path, contents).expect("the file is writable");
        path
    }

    fn spec_file(&self, entries: &[Value]) -> PathBuf {
        self.spec_file_versioned(entries, &json!(SPEC_VERSION))
    }

    fn spec_file_versioned(&self, entries: &[Value], version: &Value) -> PathBuf {
        self.write(
            "mod.py",
            &format!("import os\n\n\n{FUNCTION}\n\n\ndef other():\n    return 1\n"),
        );
        self.write(
            "formal.properties.json",
            &json!({ "version": version, "properties": entries }).to_string(),
        )
    }
}

fn load(path: &Path) -> Result<specs::SpecFile, SpecError> {
    specs::load(&path.to_string_lossy(), None)
}

fn ids(file: &specs::SpecFile) -> Vec<&str> {
    file.specs()
        .into_iter()
        .map(|spec| spec.id.as_str())
        .collect()
}

fn message(path: &Path) -> String {
    load(path).expect_err("the file is refused").to_string()
}

mod loading {
    use super::*;

    #[test]
    fn a_valid_file_yields_its_properties() {
        let workspace = Workspace::new();
        let path = workspace.spec_file(&[entry(), with(&[("id", json!("fmt_elapsed/format"))])]);
        let loaded = load(&path).expect("the file loads");
        assert_eq!(ids(&loaded), ["fmt_elapsed/bound", "fmt_elapsed/format"]);
        assert!(loaded.stale_ids().is_empty());
    }

    #[test]
    fn fields_survive_the_round_trip() {
        let workspace = Workspace::new();
        let loaded = load(&workspace.spec_file(&[entry()])).expect("the file loads");
        let spec = loaded.specs()[0];
        assert_eq!(spec.kind, "bound");
        assert_eq!(spec.formal, "forall x, 0 <= x -> fmt_elapsed x != []");
        assert_eq!(spec.assumptions, ["strings modelled as List Char"]);
    }

    #[test]
    fn a_relative_path_is_refused() {
        let error = specs::load("formal.properties.json", None).expect_err("it is refused");
        assert!(error.to_string().contains("absolute"), "{error}");
    }

    #[test]
    fn a_missing_file_is_reported() {
        let workspace = Workspace::new();
        assert!(message(&workspace.path("absent.json")).contains("no spec file"));
    }

    #[test]
    fn malformed_json_is_reported() {
        let workspace = Workspace::new();
        let path = workspace.write("formal.properties.json", "{not json");
        assert!(message(&path).contains("not valid JSON"));
    }

    #[test]
    fn a_future_version_is_refused() {
        let workspace = Workspace::new();
        let path = workspace.spec_file_versioned(&[entry()], &json!(99));
        assert_eq!(
            message(&path),
            format!(
                "{} is version 99, this formal understands 1",
                path.display()
            )
        );
    }

    #[test]
    fn an_empty_property_list_is_refused() {
        let workspace = Workspace::new();
        assert!(message(&workspace.spec_file(&[])).contains("lists no properties"));
    }

    #[test]
    fn a_missing_required_field_is_named() {
        let workspace = Workspace::new();
        let path = workspace.spec_file(&[with(&[("formal", json!("  "))])]);
        assert!(message(&path).contains("is missing formal"));
    }

    #[test]
    fn duplicate_ids_are_refused() {
        let workspace = Workspace::new();
        assert!(message(&workspace.spec_file(&[entry(), entry()])).contains("duplicate"));
    }

    #[test]
    fn an_entry_that_is_not_an_object_is_refused() {
        let workspace = Workspace::new();
        assert!(
            message(&workspace.spec_file(&[json!("a property")]))
                .contains("property 0 is not an object")
        );
    }
}

mod staleness {
    use super::*;

    fn stale_entry(source_file: &str) -> Value {
        with(&[
            ("source_file", json!(source_file)),
            ("function_code", json!(FUNCTION)),
        ])
    }

    #[test]
    fn a_spec_matching_its_source_is_live() {
        let workspace = Workspace::new();
        let loaded = load(&workspace.spec_file(&[stale_entry("mod.py")])).expect("the file loads");
        assert_eq!(ids(&loaded), ["fmt_elapsed/bound"]);
        assert!(loaded.stale_ids().is_empty());
    }

    #[test]
    fn a_spec_whose_source_changed_is_stale() {
        let workspace = Workspace::new();
        let path = workspace.spec_file(&[stale_entry("mod.py")]);
        workspace.write(
            "mod.py",
            "def fmt_elapsed(seconds):\n    return 'rewritten'\n",
        );
        let loaded = load(&path).expect("the file loads");
        assert!(loaded.specs().is_empty());
        assert_eq!(loaded.stale_ids(), ["fmt_elapsed/bound"]);
    }

    #[test]
    fn trailing_whitespace_does_not_make_a_spec_stale() {
        let workspace = Workspace::new();
        let path = workspace.spec_file(&[stale_entry("mod.py")]);
        let source = fs::read_to_string(workspace.path("mod.py")).expect("the source is readable");
        workspace.write("mod.py", &source.replace('\n', "   \n"));
        assert!(load(&path).expect("the file loads").stale_ids().is_empty());
    }

    /// Normalising rstrips each line but keeps the indentation in front of it, so a
    /// function that moves a level deeper no longer matches what was recorded. The
    /// test above is named for trailing space because that is all it changes.
    #[test]
    fn reindenting_the_file_does_make_a_spec_stale() {
        let workspace = Workspace::new();
        let path = workspace.spec_file(&[stale_entry("mod.py")]);
        let source = fs::read_to_string(workspace.path("mod.py")).expect("the source is readable");
        let deeper: Vec<String> = source.lines().map(|line| format!("    {line}")).collect();
        workspace.write("mod.py", &deeper.join("\n"));
        assert_eq!(
            load(&path).expect("the file loads").stale_ids(),
            ["fmt_elapsed/bound"]
        );
    }

    #[test]
    fn a_vanished_source_file_is_stale() {
        let workspace = Workspace::new();
        let path = workspace.spec_file(&[stale_entry("gone.py")]);
        assert_eq!(
            load(&path).expect("the file loads").stale_ids(),
            ["fmt_elapsed/bound"]
        );
    }

    #[test]
    fn a_spec_without_a_source_reference_cannot_go_stale() {
        let workspace = Workspace::new();
        assert!(
            load(&workspace.spec_file(&[entry()]))
                .expect("the file loads")
                .stale_ids()
                .is_empty()
        );
    }

    #[test]
    fn only_the_changed_property_goes_stale() {
        let workspace = Workspace::new();
        let entries = [
            with(&[
                ("id", json!("a")),
                ("source_file", json!("mod.py")),
                ("function_code", json!(FUNCTION)),
            ]),
            with(&[
                ("id", json!("b")),
                ("source_file", json!("mod.py")),
                ("function_code", json!("def other():\n    return 1")),
            ]),
        ];
        let path = workspace.spec_file(&entries);
        workspace.write("mod.py", "def other():\n    return 1\n");
        let loaded = load(&path).expect("the file loads");
        assert_eq!(ids(&loaded), ["b"]);
        assert_eq!(loaded.stale_ids(), ["a"]);
    }
}

mod proofs {
    use super::*;

    #[test]
    fn a_relative_proof_path_is_refused_by_the_id_it_was_sent_for() {
        let error =
            specs::read_proofs(&[("reverse/involutive".to_string(), "proof.lean".to_string())])
                .expect_err("it is refused");
        assert_eq!(
            error.to_string(),
            "proof file for reverse/involutive path must be absolute, got proof.lean — it is resolved by the \
             server, whose working directory is not the caller's, so a relative path may find a different file \
             or none at all"
        );
    }

    #[test]
    fn a_readable_proof_comes_back_as_its_text() {
        let workspace = Workspace::new();
        let path = workspace.write("reverse.lean", "theorem t : True := trivial\n");
        let proofs = specs::read_proofs(&[(
            "reverse/involutive".to_string(),
            path.to_string_lossy().to_string(),
        )])
        .expect("the proof is readable");
        assert_eq!(
            proofs,
            [(
                "reverse/involutive".to_string(),
                "theorem t : True := trivial\n".to_string()
            )]
        );
    }

    #[test]
    fn an_unreadable_proof_is_reported_with_the_id_that_wanted_it() {
        let workspace = Workspace::new();
        let path = workspace.path("gone.lean");
        let error = specs::read_proofs(&[(
            "reverse/involutive".to_string(),
            path.to_string_lossy().to_string(),
        )])
        .expect_err("it is refused");
        assert!(
            error
                .to_string()
                .starts_with("cannot read the proof for reverse/involutive at "),
            "{error}"
        );
    }

    #[test]
    fn the_first_bad_path_in_the_order_sent_is_the_one_reported() {
        let error = specs::read_proofs(&[
            ("first".to_string(), "a.lean".to_string()),
            ("second".to_string(), "b.lean".to_string()),
        ])
        .expect_err("it is refused");
        assert!(
            error.to_string().starts_with("proof file for first "),
            "{error}"
        );
    }
}
