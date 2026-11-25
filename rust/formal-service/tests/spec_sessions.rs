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

fn specs() -> Vec<LeanSpec> {
    let mut paths: Vec<PathBuf> = fs::read_dir(repository().join("spec"))
        .expect("the specs are listable")
        .map(|entry| entry.expect("the entry is readable").path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "lean")
        })
        .collect();
    paths.sort();
    paths.iter().map(|path| load(path)).collect()
}

fn proof_path(spec: &LeanSpec, id: &str) -> PathBuf {
    spec.proof_path(&repository().join("proofs"), id)
}

#[test]
fn every_proof_of_every_spec_holds() {
    let Some(runner) = runner() else {
        return;
    };
    let mut failed = Vec::new();
    for spec in specs() {
        let proofs: Vec<(String, String)> = spec
            .properties
            .iter()
            .map(|id| {
                (
                    id.clone(),
                    fs::read_to_string(proof_path(&spec, id)).expect("the proof is readable"),
                )
            })
            .collect();
        let dir = TempDir::new().expect("a temporary directory");
        let checked = check(&runner, &dir, spec, &proofs);
        assert_eq!(checked.outcomes.len(), proofs.len());
        failed.extend(
            checked
                .outcomes
                .iter()
                .filter(|outcome| !outcome.verified())
                .map(|outcome| format!("{}: {}", outcome.id, outcome.error)),
        );
    }
    assert!(failed.is_empty(), "{}", failed.join("\n"));
}

#[test]
fn every_proof_answers_a_property_of_its_spec() {
    let mut orphans = Vec::new();
    for spec in specs() {
        let names: Vec<&str> = spec.properties.iter().map(|id| name(&spec, id)).collect();
        orphans.extend(
            fs::read_dir(repository().join("proofs").join(&spec.namespace))
                .expect("the proofs are listable")
                .map(|entry| entry.expect("the entry is readable").path())
                .filter(|path| {
                    path.extension().is_none_or(|extension| extension != "lean")
                        || path
                            .file_stem()
                            .is_none_or(|stem| !names.iter().any(|name| stem == *name))
                })
                .map(|path| path.display().to_string()),
        );
    }
    assert!(
        orphans.is_empty(),
        "these proofs answer no property of their spec: {}",
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

const BOUNDED: &str = "namespace Bounded\n\ninductive Action where\n  | inc\n  | reset\n\nstructure State where\n  count : Nat\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .inc => ⟨min (s.count + 1) 2⟩\n  | .reset => ⟨0⟩\n\ndef count_at_most_two : State → Prop := fun s => s.count ≤ 2\n\ndef count_below_two : State → Prop := fun s => s.count < 2\n\nend Bounded\n";

#[test]
fn an_invariant_of_a_machine_holds_in_every_reachable_state_and_a_false_one_never_does() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = TempDir::new().expect("a temporary directory");
    let path = dir.path().join("Bounded.lean");
    fs::write(&path, BOUNDED).expect("written");
    let spec = load(&path);
    assert_eq!(
        spec.properties,
        [
            "Bounded.count_at_most_two.always",
            "Bounded.count_below_two.always"
        ]
    );
    let holds = "namespace Bounded\n\ntheorem count_at_most_two.always.holds : count_at_most_two.always := by\n  unfold count_at_most_two.always run\n  have key : ∀ (actions : List Action) (s : State), count_at_most_two s →\n      count_at_most_two (actions.foldl step s) := by\n    intro actions\n    induction actions with\n    | nil => intro s h; exact h\n    | cons a rest ih =>\n      intro s h\n      apply ih\n      cases a <;> simp [step, count_at_most_two] at * <;> omega\n  intro actions\n  exact key actions init (by simp [count_at_most_two, init])\n\nend Bounded\n";
    let wrong = "namespace Bounded\n\ntheorem count_below_two.always.holds : count_below_two.always := by\n  unfold count_below_two.always run count_below_two\n  intro actions\n  omega\n\nend Bounded\n";
    let checked = check(
        &runner,
        &dir,
        spec,
        &[
            (
                "Bounded.count_at_most_two.always".to_string(),
                holds.to_string(),
            ),
            (
                "Bounded.count_below_two.always".to_string(),
                wrong.to_string(),
            ),
        ],
    );
    let verified: Vec<&str> = checked
        .outcomes
        .iter()
        .filter(|outcome| outcome.verified())
        .map(|outcome| outcome.id.as_str())
        .collect();
    assert_eq!(
        verified,
        ["Bounded.count_at_most_two.always"],
        "{:?}",
        checked
            .outcomes
            .iter()
            .map(|outcome| &outcome.error)
            .collect::<Vec<_>>()
    );
}

#[test]
fn opening_a_session_on_a_machine_explores_it_to_its_depth() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = TempDir::new().expect("a temporary directory");
    let path = dir.path().join("Bounded.lean");
    fs::write(&path, BOUNDED).expect("written");
    let cache = ProofCache::new(dir.path().join("cache"), Duration::from_hours(1));
    let session = Sessions::default()
        .open_spec(&runner, &cache, load(&path))
        .expect("the spec compares nothing");
    let session = session.lock().expect("a fresh session");
    let bounded: Vec<(&str, u32, u32)> = session
        .bounded
        .iter()
        .map(|bound| (bound.id.as_str(), bound.depth, bound.states))
        .collect();
    assert_eq!(bounded, [("Bounded.count_at_most_two.always", 10, 3)]);
    let refuted: Vec<(&str, &[String])> = session
        .refuted
        .iter()
        .map(|refutation| (refutation.id.as_str(), refutation.counterexample.as_slice()))
        .collect();
    assert_eq!(
        refuted,
        [(
            "Bounded.count_below_two.always",
            &["actions := [Bounded.Action.inc, Bounded.Action.inc]".to_string()][..]
        )]
    );
}

type Bounds = Vec<(String, u32, u32)>;

type Refutations = Vec<(String, Vec<String>)>;

fn explored(runner: &Runner, text: &str) -> (Bounds, Refutations) {
    let dir = TempDir::new().expect("a temporary directory");
    let path = dir.path().join("Explored.lean");
    fs::write(&path, text).expect("written");
    let cache = ProofCache::new(dir.path().join("cache"), Duration::from_hours(1));
    let session = Sessions::default()
        .open_spec(runner, &cache, load(&path))
        .expect("the spec compares nothing");
    let session = session.lock().expect("a fresh session");
    (
        session
            .bounded
            .iter()
            .map(|bound| (bound.id.clone(), bound.depth, bound.states))
            .collect(),
        session
            .refuted
            .iter()
            .map(|refutation| (refutation.id.clone(), refutation.counterexample.clone()))
            .collect(),
    )
}

#[test]
fn the_exploration_answers_every_shape_of_machine_it_reads() {
    let Some(runner) = runner() else {
        return;
    };
    let gap = BOUNDED
        .replace("  | reset\n", "  | reset\n\n  | jump\n")
        .replace("  | .reset => ⟨0⟩", "  | .reset => ⟨0⟩\n  | .jump => ⟨5⟩")
        .replace(
            "def count_below_two : State → Prop := fun s => s.count < 2\n\n",
            "",
        );
    assert_eq!(
        explored(&runner, &gap).1,
        [(
            "Bounded.count_at_most_two.always".to_string(),
            vec!["actions := [Bounded.Action.jump]".to_string()]
        )]
    );

    let sampled = BOUNDED
        .replace("  | inc\n", "  | add (n : Nat)\n")
        .replace("  | .inc => ⟨min (s.count + 1) 2⟩", "  | .add n => ⟨min (s.count + n) 2⟩")
        .replace(
            "end Bounded",
            "def Action.samples : List Action := [.add 1, .add 2, .reset]\n\ndef depth : Nat := 3\n\nend Bounded",
        );
    let (bounded, refuted) = explored(&runner, &sampled);
    assert_eq!(
        bounded,
        [("Bounded.count_at_most_two.always".to_string(), 3, 3)]
    );
    assert_eq!(
        refuted,
        [(
            "Bounded.count_below_two.always".to_string(),
            vec!["actions := [Bounded.Action.add 2]".to_string()]
        )]
    );

    let false_at_init = BOUNDED.replace("def init : State := ⟨0⟩", "def init : State := ⟨3⟩");
    let refuted = explored(&runner, &false_at_init).1;
    assert!(
        refuted.contains(&(
            "Bounded.count_below_two.always".to_string(),
            vec!["actions := []".to_string()]
        )),
        "{refuted:?}"
    );

    let wide = "namespace Wide\n\ninductive Action where\n  | a\n  | b\n  | c\n  | d\n  | e\n  | f\n\nstructure State where\n  history : List Nat\n\ndef init : State := ⟨[]⟩\n\ndef step (s : State) : Action → State\n  | .a => ⟨0 :: s.history⟩\n  | .b => ⟨1 :: s.history⟩\n  | .c => ⟨2 :: s.history⟩\n  | .d => ⟨3 :: s.history⟩\n  | .e => ⟨4 :: s.history⟩\n  | .f => ⟨5 :: s.history⟩\n\ndef short : State → Prop := fun s => s.history.length ≤ 20\n\nend Wide\n";
    let bounded = explored(&runner, wide).0;
    let [(id, depth, states)] = bounded.as_slice() else {
        panic!("one bound, got {bounded:?}");
    };
    assert_eq!(id, "Wide.short.always");
    assert!(*depth < 10 && *states > 100_000, "{bounded:?}");
}

#[test]
fn the_code_of_a_machine_replays_one_trace_per_state_and_a_difference_names_it() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = TempDir::new().expect("a temporary directory");
    let path = dir.path().join("Bounded.lean");
    fs::write(
        &path,
        BOUNDED.replace(
            "def step (s : State) : Action → State",
            "/-- code: src/bounded.rs step -/\ndef step (s : State) : Action → State",
        ),
    )
    .expect("written");
    let cache = ProofCache::new(dir.path().join("cache"), Duration::from_hours(1));
    let session = Sessions::default()
        .open_spec(&runner, &cache, load(&path))
        .expect("Lean evaluates the traces");
    let session = session.lock().expect("a fresh session");
    let [replay] = session.evaluated.as_slice() else {
        panic!("one compared function, got {:?}", session.evaluated);
    };
    assert_eq!(replay.function, "Bounded.run");
    assert_eq!(replay.code, "src/bounded.rs step");
    assert_eq!(
        replay.inputs,
        [
            serde_json::json!([]),
            serde_json::json!(["inc"]),
            serde_json::json!(["inc", "inc"])
        ]
    );
    let states = |counts: &[u64]| -> Vec<serde_json::Value> {
        counts
            .iter()
            .map(|count| serde_json::json!({ "count": count }))
            .collect()
    };
    let matched = session
        .compare(&[("Bounded.run".to_string(), states(&[0, 1, 2]))])
        .expect("the machine is compared");
    assert_eq!(matched.matched, ["Bounded.run"]);
    let differed = session
        .compare(&[("Bounded.run".to_string(), states(&[0, 1, 3]))])
        .expect("the machine is compared");
    let [difference] = differed.differed.as_slice() else {
        panic!("one difference, got {:?}", differed.differed);
    };
    assert_eq!(difference.input, serde_json::json!(["inc", "inc"]));
    assert_eq!(difference.spec, serde_json::json!({ "count": 2 }));
    assert_eq!(difference.code, serde_json::json!({ "count": 3 }));
}

#[test]
fn a_replayed_machine_with_text_in_its_state_and_an_unrelated_type_still_opens() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = TempDir::new().expect("a temporary directory");
    let path = dir.path().join("Typed.lean");
    fs::write(
        &path,
        "namespace Typed\n\ninductive Action where\n  | a\n  | clear\n\nstructure State where\n  text : List Char\n\nstructure Config where\n  pick : Nat → Nat\n\ndef init : State := ⟨[]⟩\n\n/-- code: src/typed.rs step -/\ndef step (s : State) : Action → State\n  | .a => ⟨if s.text.length < 2 then 'a' :: s.text else s.text⟩\n  | .clear => ⟨[]⟩\n\ndef short : State → Prop := fun s => s.text.length ≤ 2\n\nend Typed\n",
    )
    .expect("written");
    let cache = ProofCache::new(dir.path().join("cache"), Duration::from_hours(1));
    let session = Sessions::default()
        .open_spec(&runner, &cache, load(&path))
        .expect("the unrelated type does not refuse the session");
    let session = session.lock().expect("a fresh session");
    let [replay] = session.evaluated.as_slice() else {
        panic!("one compared function, got {:?}", session.evaluated);
    };
    assert_eq!(
        replay.answers,
        [
            serde_json::json!({ "text": "" }),
            serde_json::json!({ "text": "a" }),
            serde_json::json!({ "text": "aa" })
        ]
    );
}

const CYCLE: &str = "namespace Cycle\n\ninductive Action where\n  | inc\n  | reset\n\nstructure State where\n  count : Nat\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .inc => ⟨if s.count = 2 then 0 else s.count + 1⟩\n  | .reset => ⟨0⟩\n\ndef count_at_most_two : State → Prop := fun s => s.count ≤ 2\n\ndef count_is_not_five : State → Prop := fun s => s.count ≠ 5\n\nend Cycle\n";

#[test]
fn an_invariant_a_step_breaks_from_an_unreachable_state_comes_back_with_that_state() {
    let Some(runner) = runner() else {
        return;
    };
    let dir = TempDir::new().expect("a temporary directory");
    let path = dir.path().join("Cycle.lean");
    fs::write(&path, CYCLE).expect("written");
    let cache = ProofCache::new(dir.path().join("cache"), Duration::from_hours(1));
    let session = Sessions::default()
        .open_spec(&runner, &cache, load(&path))
        .expect("the spec compares nothing");
    let session = session.lock().expect("a fresh session");
    assert_eq!(session.refuted, []);
    let found: Vec<(&str, &str, &str, &str)> = session
        .not_inductive
        .iter()
        .map(|found| {
            (
                found.id.as_str(),
                found.state.as_str(),
                found.action.as_str(),
                found.next.as_str(),
            )
        })
        .collect();
    assert_eq!(
        found,
        [(
            "Cycle.count_is_not_five.always",
            "{ count := 4 }",
            "Cycle.Action.inc",
            "{ count := 5 }"
        )]
    );
    assert_eq!(
        session.inductive_together,
        [
            "Cycle.count_at_most_two.always",
            "Cycle.count_is_not_five.always"
        ]
    );
}

fn failing(runner: &Runner, name: &str, spec: &str, proofs: &[(&str, &str)]) -> Vec<String> {
    let dir = TempDir::new().expect("a temporary directory");
    let path = dir.path().join(format!("{name}.lean"));
    fs::write(&path, spec).expect("written");
    let proofs: Vec<(String, String)> = proofs
        .iter()
        .map(|(id, proof)| (format!("{name}.{id}"), (*proof).to_string()))
        .collect();
    let checked = check(runner, &dir, load(&path), &proofs);
    assert_eq!(checked.outcomes.len(), proofs.len());
    checked
        .outcomes
        .iter()
        .filter(|outcome| !outcome.verified())
        .map(|outcome| outcome.id.clone())
        .collect()
}

#[test]
fn a_spec_proves_safety_and_liveness_with_formal_s_temporal_library() {
    let Some(runner) = runner() else {
        return;
    };
    let live = "import Formal.Temporal\n\nnamespace Live\n\ninductive Action where\n  | inc\n  | reset\n\nstructure State where\n  count : Nat\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .inc => ⟨min (s.count + 1) 2⟩\n  | .reset => ⟨0⟩\n\ndef count_stays_small : Prop := Temporal.always init step (fun s => s.count ≤ 2)\n\ndef a_fair_reset_empties_the_count : Prop :=\n  Temporal.leadsTo init step (Temporal.fair Action.reset) (fun s => 0 < s.count) (fun s => s.count = 0)\n\ndef a_reset_empties_the_count_without_fairness : Prop :=\n  Temporal.leadsTo init step (fun _ => True) (fun s => 0 < s.count) (fun s => s.count = 0)\n\ndef unfairness_breaks_it : Prop := ¬ a_reset_empties_the_count_without_fairness\n\nend Live\n";
    let always = "namespace Live\n\ntheorem count_stays_small.holds : count_stays_small :=\n  Temporal.always_of_inductive (by simp [init]) (by\n    intro s a h\n    cases a <;> simp [step] <;> omega)\n\nend Live\n";
    let leads = "namespace Live\n\ntheorem a_fair_reset_empties_the_count.holds : a_fair_reset_empties_the_count :=\n  Temporal.leadsTo_of_fair_step Action.reset (fun _ fair => fair) ⟨_, Temporal.fair_constant Action.reset⟩\n    Temporal.always_true\n    (by\n      intro s b _ _ _\n      cases b <;> simp [step] <;> omega)\n    (by\n      intro s _ _ _\n      simp [step])\n\nend Live\n";
    let broken = "namespace Live\n\ntheorem unfairness_breaks_it.holds : unfairness_breaks_it := by\n  unfold unfairness_breaks_it a_reset_empties_the_count_without_fairness Temporal.leadsTo\n  intro ⟨_, leads⟩\n  have positive : ∀ m, 0 < (Temporal.states init step (fun _ => Action.inc) (m + 1)).count := by\n    intro m\n    simp only [Temporal.states, step]\n    omega\n  obtain ⟨m, hm, empty⟩ := leads (fun _ => Action.inc) trivial 1 (by simp [Temporal.states, step, init])\n  have := positive (m - 1)\n  rw [show m - 1 + 1 = m by omega] at this\n  omega\n\nend Live\n";
    let unfair = leads.replace(
        "a_fair_reset_empties_the_count",
        "a_reset_empties_the_count_without_fairness",
    );
    assert_eq!(
        failing(
            &runner,
            "Live",
            live,
            &[
                ("count_stays_small", always),
                ("a_fair_reset_empties_the_count", leads),
                ("a_reset_empties_the_count_without_fairness", &unfair),
                ("unfairness_breaks_it", broken),
            ],
        ),
        ["Live.a_reset_empties_the_count_without_fairness"]
    );
}

#[test]
fn a_decreasing_measure_proves_that_a_fair_drain_empties_the_tank() {
    let Some(runner) = runner() else {
        return;
    };
    let drain = "import Formal.Temporal\n\nnamespace Drain\n\ninductive Action where\n  | drain\n  | wait\n\nstructure State where\n  level : Nat\n\ndef init : State := ⟨3⟩\n\ndef step (s : State) : Action → State\n  | .drain => ⟨s.level - 1⟩\n  | .wait => s\n\ndef a_full_tank_empties : Prop :=\n  Temporal.leadsTo init step (Temporal.fair Action.drain) (fun s => 0 < s.level) (fun s => s.level = 0)\n\ndef the_tank_empties : Prop :=\n  Temporal.eventually init step (Temporal.fair Action.drain) (fun s => s.level = 0)\n\ndef draining_while_waiting_empties_it : Prop :=\n  Temporal.leadsTo init step (fun run => Temporal.fair Action.drain run ∧ Temporal.fair Action.wait run)\n    (fun s => 0 < s.level) (fun s => s.level = 0)\n\nend Drain\n";
    let leads = "namespace Drain\n\ntheorem a_full_tank_empties.holds : a_full_tank_empties :=\n  Temporal.leadsTo_of_measure Action.drain (fun _ fair => fair) ⟨_, Temporal.fair_constant Action.drain⟩\n    Temporal.always_true\n    (fun s => s.level)\n    (by\n      intro s b _ _ _\n      cases b <;> simp [step] <;> omega)\n    (by\n      intro s _ _ _\n      simp [step]\n      omega)\n\nend Drain\n";
    let eventually = "namespace Drain\n\ntheorem the_tank_empties.holds : the_tank_empties :=\n  Temporal.eventually_of_leadsTo (p := fun (s : State) => 0 < s.level) (by simp [init]) a_full_tank_empties.holds\n\nend Drain\n";
    let both = format!("{leads}\n{eventually}");
    let two = leads
        .replace("a_full_tank_empties", "draining_while_waiting_empties_it")
        .replace(
            "(fun _ fair => fair) ⟨_, Temporal.fair_constant Action.drain⟩",
            "(fun _ fair => fair.1)\n    ⟨_, Temporal.fair_cycle Action.drain [Action.wait] Action.drain (by simp),\n      Temporal.fair_cycle Action.drain [Action.wait] Action.wait (by simp)⟩",
        );
    assert_eq!(
        failing(
            &runner,
            "Drain",
            drain,
            &[
                ("a_full_tank_empties", leads),
                ("the_tank_empties", &both),
                ("draining_while_waiting_empties_it", &two),
            ],
        ),
        Vec::<String>::new()
    );
}

#[test]
fn no_temporal_property_holds_for_want_of_a_run() {
    let Some(runner) = runner() else {
        return;
    };
    let empty = "import Formal.Temporal\n\nnamespace Empty\n\ninductive Action where\n\ndef init_breaks_it : Prop :=\n  Temporal.always (1 : Nat) (fun n (_ : Action) => n) (fun n => n = 0)\n\ndef seven_comes_with_no_run : Prop :=\n  Temporal.eventually (1 : Nat) (fun n (_ : Bool) => n) (fun _ => False) (fun n => n = 7)\n\nend Empty\n";
    let no_action = "namespace Empty\n\ntheorem init_breaks_it.holds : init_breaks_it := fun run _ => nomatch run 0\n\nend Empty\n";
    let no_run = "namespace Empty\n\ntheorem seven_comes_with_no_run.holds : seven_comes_with_no_run :=\n  ⟨by simp, fun _ impossible => impossible.elim⟩\n\nend Empty\n";
    assert_eq!(
        failing(
            &runner,
            "Empty",
            empty,
            &[
                ("init_breaks_it", no_action),
                ("seven_comes_with_no_run", no_run),
            ],
        ),
        ["Empty.init_breaks_it", "Empty.seven_comes_with_no_run"]
    );
}

fn liveness_answers(
    runner: &Runner,
    name: &str,
    spec: &str,
) -> (Vec<(String, Vec<String>)>, Vec<String>) {
    let dir = TempDir::new().expect("a temporary directory");
    let path = dir.path().join(format!("{name}.lean"));
    fs::write(&path, spec).expect("written");
    let cache = ProofCache::new(dir.path().join("cache"), Duration::from_hours(1));
    let session = Sessions::default()
        .open_spec(runner, &cache, load(&path))
        .expect("the spec compares nothing");
    let session = session.lock().expect("a fresh session");
    (
        session
            .refuted
            .iter()
            .map(|refutation| (refutation.id.clone(), refutation.counterexample.clone()))
            .collect(),
        session
            .bounded
            .iter()
            .map(|bound| bound.id.clone())
            .collect(),
    )
}

#[test]
fn a_false_liveness_property_comes_back_with_a_fair_run_that_never_reaches_its_goal() {
    let Some(runner) = runner() else {
        return;
    };
    let live = "import Formal.Temporal\n\nnamespace Live\n\ninductive Action where\n  | inc\n  | reset\n\nstructure State where\n  count : Nat\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .inc => ⟨min (s.count + 1) 2⟩\n  | .reset => ⟨0⟩\n\ndef a_fair_reset_empties_the_count : Prop :=\n  Temporal.leadsTo init step (Temporal.fair Action.reset) (fun s => 0 < s.count) (fun s => s.count = 0)\n\ndef a_reset_empties_the_count_without_fairness : Prop :=\n  Temporal.leadsTo init step (fun _ => True) (fun s => 0 < s.count) (fun s => s.count = 0)\n\nend Live\n";
    let (refuted, bounded) = liveness_answers(&runner, "Live", live);
    assert_eq!(
        refuted,
        [(
            "Live.a_reset_empties_the_count_without_fairness".to_string(),
            vec![
                "actions := [Live.Action.inc, Live.Action.inc]".to_string(),
                "then forever := [Live.Action.inc]".to_string()
            ]
        )]
    );
    assert_eq!(bounded, ["Live.a_fair_reset_empties_the_count"]);
}

#[test]
fn a_liveness_property_on_a_walk_cut_at_its_depth_gets_no_answer() {
    let Some(runner) = runner() else {
        return;
    };
    let climb = "import Formal.Temporal\n\nnamespace Climb\n\ninductive Action where\n  | up\n\nstructure State where\n  height : Nat\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .up => ⟨s.height + 1⟩\n\ndef the_top_comes : Prop :=\n  Temporal.leadsTo init step (Temporal.fair Action.up) (fun s => s.height < 1000) (fun s => s.height = 1000)\n\nend Climb\n";
    let (refuted, bounded) = liveness_answers(&runner, "Climb", climb);
    assert_eq!(refuted, Vec::<(String, Vec<String>)>::new());
    assert_eq!(bounded, Vec::<String>::new());
}

#[test]
fn a_liveness_property_over_thousands_of_states_naming_the_spec_s_own_max_is_bounded() {
    let Some(runner) = runner() else {
        return;
    };
    let climb = "import Formal.Temporal\n\nnamespace Climb\n\ninductive Action where\n  | up\n\nstructure State where\n  height : Nat\n\ndef max : Nat := 5000\n\ndef depth : Nat := 5100\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .up => ⟨min (s.height + 1) max⟩\n\ndef the_top_comes : Prop :=\n  Temporal.leadsTo init step (Temporal.fair Action.up) (fun s => s.height < max) (fun s => s.height = max)\n\nend Climb\n";
    let (refuted, bounded) = liveness_answers(&runner, "Climb", climb);
    assert_eq!(refuted, Vec::<(String, Vec<String>)>::new());
    assert_eq!(bounded, ["Climb.the_top_comes"]);
}

#[test]
fn a_liveness_property_whose_fair_action_the_samples_leave_out_is_not_bounded() {
    let Some(runner) = runner() else {
        return;
    };
    let add = "import Formal.Temporal\n\nnamespace Add\n\ninductive Action where\n  | add (n : Nat)\n  | reset\n\nstructure State where\n  count : Nat\n\ndef Action.samples : List Action := [Action.reset]\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .add n => ⟨min (s.count + n) 3⟩\n  | .reset => ⟨0⟩\n\ndef two_comes : Prop :=\n  Temporal.eventually init step (Temporal.fair (Action.add 1)) (fun s => s.count = 2)\n\nend Add\n";
    let (_, bounded) = liveness_answers(&runner, "Add", add);
    assert_eq!(bounded, Vec::<String>::new());
}

#[test]
fn a_lasso_is_reached_through_other_states_and_takes_every_fair_action_beside_an_invariant() {
    let Some(runner) = runner() else {
        return;
    };
    let mix = "import Formal.Temporal\n\nnamespace Mix\n\ninductive Action where\n  | down\n  | bounce\n\nstructure State where\n  n : Nat\n\ndef init : State := ⟨5⟩\n\ndef step (s : State) : Action → State\n  | .down => ⟨s.n - 1⟩\n  | .bounce => ⟨if s.n = 2 then 3 else s.n - 1⟩\n\ndef at_most_five (s : State) : Prop := s.n ≤ 5\n\ndef a_fair_bounce_empties_it : Prop :=\n  Temporal.leadsTo init step (Temporal.fair Action.bounce) (fun s => s.n = 5) (fun s => s.n = 0)\n\ndef fair_down_and_bounce_empty_it : Prop :=\n  Temporal.eventually init step (fun run => Temporal.fair Action.down run ∧ Temporal.fair Action.bounce run)\n    (fun s => s.n = 0)\n\nend Mix\n";
    let (refuted, bounded) = liveness_answers(&runner, "Mix", mix);
    assert_eq!(
        refuted,
        [
            (
                "Mix.a_fair_bounce_empties_it".to_string(),
                vec![
                    "actions := [Mix.Action.down, Mix.Action.down]".to_string(),
                    "then forever := [Mix.Action.bounce, Mix.Action.bounce]".to_string()
                ]
            ),
            (
                "Mix.fair_down_and_bounce_empty_it".to_string(),
                vec![
                    "actions := [Mix.Action.down, Mix.Action.down]".to_string(),
                    "then forever := [Mix.Action.down, Mix.Action.bounce]".to_string()
                ]
            ),
        ]
    );
    assert_eq!(bounded, ["Mix.at_most_five.always"]);
}
