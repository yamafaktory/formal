//! Sessions on a Lean spec, checked by a real Lean.

use std::{
    fs,
    path::{
        Path,
        PathBuf,
    },
    time::Duration,
};

use formal_core::{
    hints::Table,
    lean_spec::LeanSpec,
};
use formal_lean::run::Runner;
use formal_service::{
    cache::ProofCache,
    checker::{
        Checker,
        Outcome,
    },
    session::Sessions,
};
use tempfile::TempDir;

const DEMO: &str = include_str!("../../../tests/fixtures/lean_spec/Demo.lean");

fn runner() -> Option<Runner> {
    let runner = Runner::from_env();
    let project = &runner.paths().lean_project_dir;
    (project.join("lakefile.toml").is_file() && project.join(".lake").is_dir()).then_some(runner)
}

fn repository() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn load(path: &Path) -> LeanSpec {
    LeanSpec::load(&path.to_string_lossy()).expect("the spec loads")
}

fn demo_with(dir: &TempDir, extra: &str) -> LeanSpec {
    let path = dir.path().join("Demo.lean");
    fs::write(
        &path,
        DEMO.replace("end Demo", &format!("{extra}\n\nend Demo")),
    )
    .expect("written");
    load(&path)
}

struct Checked {
    outcomes: Vec<Outcome>,
    accepted: Vec<(String, String)>,
}

fn check(runner: &Runner, dir: &TempDir, spec: LeanSpec, proofs: &[(String, String)]) -> Checked {
    let cache = ProofCache::new(dir.path().join("cache"), Duration::from_hours(1));
    let table = Table::shipped().expect("the shipped table is valid");
    let session = Sessions::default()
        .open_spec(runner, &cache, spec)
        .expect("Lean evaluates the spec");
    let mut session = session.lock().expect("a fresh session");
    let outcomes = session
        .check(&Checker::new(runner, table), &cache, proofs)
        .expect("every property is registered");
    let mut accepted: Vec<(String, String)> = session.verified.clone().into_iter().collect();
    accepted.sort();
    Checked { outcomes, accepted }
}

fn name<'a>(spec: &LeanSpec, id: &'a str) -> &'a str {
    id.strip_prefix(&format!("{}.", spec.namespace))
        .expect("an id is under the spec's namespace")
}

fn proof(id: &str, lean: &str) -> Vec<(String, String)> {
    vec![(id.to_string(), lean.to_string())]
}

#[test]
fn every_proof_of_the_spec_holds() {
    let Some(runner) = runner() else {
        return;
    };
    let spec = load(&repository().join("spec/Pystr.lean"));
    let proofs: Vec<(String, String)> = spec
        .properties
        .iter()
        .map(|id| {
            let path = repository()
                .join("proofs")
                .join(&spec.namespace)
                .join(format!("{}.lean", name(&spec, id)));
            (
                id.clone(),
                fs::read_to_string(path).expect("the proof is readable"),
            )
        })
        .collect();

    let dir = TempDir::new().expect("a temporary directory");
    let checked = check(&runner, &dir, spec, &proofs);
    let failed: Vec<String> = checked
        .outcomes
        .iter()
        .filter(|outcome| !outcome.verified())
        .map(|outcome| format!("{}: {}", outcome.id, outcome.error))
        .collect();
    assert!(failed.is_empty(), "{}", failed.join("\n"));
    assert_eq!(checked.outcomes.len(), proofs.len());
}

#[test]
fn every_proof_answers_a_property_of_the_spec() {
    let spec = load(&repository().join("spec/Pystr.lean"));
    let names: Vec<&str> = spec.properties.iter().map(|id| name(&spec, id)).collect();
    let orphans: Vec<String> = fs::read_dir(repository().join("proofs").join(&spec.namespace))
        .expect("the proofs are listable")
        .map(|entry| entry.expect("the entry is readable").path())
        .filter(|path| {
            path.extension().is_none_or(|extension| extension != "lean")
                || path
                    .file_stem()
                    .is_none_or(|stem| !names.iter().any(|name| stem == *name))
        })
        .map(|path| path.display().to_string())
        .collect();
    assert!(
        orphans.is_empty(),
        "these proofs answer no property of the spec: {}",
        orphans.join(", ")
    );
}

#[test]
fn a_false_property_is_never_verified() {
    let Some(runner) = runner() else {
        return;
    };
    let false_property = "def double_odd : Prop := ∀ n, double n % 2 = 1";
    let cheats = [
        "import Mathlib\n\nnamespace Demo\ntheorem double_odd.holds : True := trivial\nend Demo\nnotation \"_root_.Demo.double_odd\" => True\n",
        "import Mathlib\n\nclass Given (p : Prop) : Prop where\n  out : p\nvariable [h : Given _root_.Demo.double_odd]\ninclude h\ntheorem _root_.Demo.double_odd.holds : _root_.Demo.double_odd := h.out\n",
        "import Mathlib\n\nnamespace Cheat\ndef Demo.double_odd : Prop := True\ntheorem Demo.double_odd.holds : Demo.double_odd := trivial\n",
        "import Mathlib\n\ninfix:50 (priority := high) \" == \" => fun _ _ => true\n\ntheorem Demo.double_odd.holds : True := trivial\n",
        "import Mathlib\n\ninfixl:65 (priority := high) \" ++ \" => fun _ b => b\nset_option warn.sorry false\n\ntheorem Demo.double_odd.holds : Demo.double_odd := sorry\n",
        "import Mathlib /-\n-/\nnamespace Demo\ndef double_odd : Prop := True\ntheorem double_odd.holds : double_odd := trivial\nend Demo\n",
        "import Mathlib instance (priority := high) fakeOne : OfNat Nat 1 := ⟨0⟩\n\nnamespace Demo\ntheorem double_odd.holds : double_odd := by\n  intro n\n  show (n + n) % 2 = 0\n  omega\nend Demo\n",
        "import Mathlib\n\nset_option debug.skipKernelTC true in\ntheorem Demo.double_odd.holds : Demo.double_odd := by\n  intro n\n  show Demo.double n % 2 = 1\n  decide +kernel\n",
    ];
    for cheat in cheats {
        let dir = TempDir::new().expect("a temporary directory");
        let checked = check(
            &runner,
            &dir,
            demo_with(&dir, false_property),
            &proof("Demo.double_odd", cheat),
        );
        assert!(
            checked.outcomes.iter().all(|outcome| !outcome.verified()),
            "verified by:\n{cheat}"
        );
    }
}

#[test]
fn an_error_names_the_line_of_the_proof() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = TempDir::new().expect("a temporary directory");
    let lean = "import Mathlib\n\nnamespace Demo\n\ntheorem double_even.holds : double_even := by\n  intro n\n  exact rfl\n\nend Demo\n";
    let checked = check(
        &runner,
        &dir,
        demo_with(&dir, ""),
        &proof("Demo.double_even", lean),
    );
    let outcome = checked.outcomes.first().expect("one outcome");
    assert!(!outcome.verified());
    assert_eq!(outcome.line, Some(7), "{}", outcome.error);
}

#[test]
fn a_failed_tactic_is_recovered_and_the_proof_is_kept_without_the_spec() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = TempDir::new().expect("a temporary directory");
    let lean = "import Mathlib\n\nnamespace Demo\n\ntheorem two.holds : two := by\n  exact Nat.lt_irrefl 0\n\nend Demo\n";
    let checked = check(
        &runner,
        &dir,
        demo_with(&dir, "def two : Prop := 1 + 1 = 2"),
        &proof("Demo.two", lean),
    );
    let outcome = checked.outcomes.first().expect("one outcome");
    assert!(outcome.verified(), "{}", outcome.error);
    assert!(outcome.recovered);
    let (_, accepted) = checked.accepted.first().expect("one accepted proof");
    assert!(!accepted.contains("def double"), "{accepted}");
    assert!(accepted.contains("theorem two.holds"), "{accepted}");
}

#[test]
fn a_property_over_any_universe_can_be_proved() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = TempDir::new().expect("a temporary directory");
    let lean = "/- A proof with a header, as Mathlib writes them. -/\nimport Mathlib\n\nnamespace Demo\n\ntheorem map_id.holds : map_id := by\n  intro α l\n  simp\n\nend Demo\n";
    let checked = check(
        &runner,
        &dir,
        demo_with(
            &dir,
            "universe u\n\ndef map_id : Prop := ∀ (α : Type u) (l : List α), l.map id = l",
        ),
        &proof("Demo.map_id", lean),
    );
    let outcome = checked.outcomes.first().expect("one outcome");
    assert!(outcome.verified(), "{}", outcome.error);
}

#[test]
fn a_spec_that_imports_another_spec_proves_against_its_definitions() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = TempDir::new().expect("a temporary directory");
    fs::copy(
        repository().join("spec/Pystr.lean"),
        dir.path().join("Pystr.lean"),
    )
    .expect("copied");
    let path = dir.path().join("Uses.lean");
    fs::write(
        &path,
        "import Spec.Pystr\n\nnamespace Uses\n\ndef rstrip_drops_a_trailing_tab : Prop := Pystr.rstrip ['a', '\\t'] = ['a']\n\nend Uses\n",
    )
    .expect("written");
    let lean = "namespace Uses\n\ntheorem rstrip_drops_a_trailing_tab.holds : rstrip_drops_a_trailing_tab := by\n  decide\n\nend Uses\n";
    let checked = check(
        &runner,
        &dir,
        load(&path),
        &proof("Uses.rstrip_drops_a_trailing_tab", lean),
    );
    let [outcome] = checked.outcomes.as_slice() else {
        panic!("one outcome, got {}", checked.outcomes.len());
    };
    assert!(outcome.verified(), "{}", outcome.error);
}
