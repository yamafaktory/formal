//! A spec written in Lean, and the file formal checks a proof of it in.

use std::{
    collections::HashMap,
    fs,
    path::{
        Path,
        PathBuf,
    },
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
        lean_spec_search_key,
    },
    property::PropertySpec,
    pystr,
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

const SEARCH_IMPORT: &str = "Plausible";

const ALWAYS: &str = "always";

const EXPLORATION_IMPORT: &str = "Std.Data.HashSet";

const EXPLORATION_MARK: &str = "formal-bounded";

const STATE_BUDGET: u32 = 100_000;

const INDUCTION_MARK: &str = "formal-inductive";

const INDUCTION_TRIES: u32 = 1_000;

const INDUCTION_HELPERS: &str = "namespace FormalInductive

def search {σ α : Type} (draw : Plausible.Gen σ) (step : σ → α → σ) (actions : List α)
    (holds : σ → Bool) (tries : Nat) : IO (Option (σ × α × σ) × Nat) := do
  let mut held := 0
  for i in [0:tries] do
    let s ← Plausible.Gen.run draw (i % 100)
    if holds s then
      held := held + 1
      for a in actions do
        let t := step s a
        if !holds t then return (some (s, a, t), held)
  return (none, held)

def report {σ α : Type} [Repr σ] [Repr α] (mark key : String) : Option (σ × α × σ) × Nat → String
  | (some (s, a, t), _) => s!\"{mark} {key} broken\\x1f{reprStr s}\\x1f{reprStr a}\\x1f{reprStr t}\"
  | (none, held) => s!\"{mark} {key} kept {held}\"

end FormalInductive";

const DEFAULT_DEPTH: &str = "10";

const EXPLORATION_HELPERS: &str = "namespace FormalBounded

def complete {α : Type} (actions : List α) (_ : ∀ a, a ∈ actions) : List α := actions

def walk {σ α : Type} [BEq σ] [Hashable σ] (init : σ) (step : σ → α → σ) (actions : List α)
    (holds : σ → Bool) (depth budget : Nat) : Option (List α) × Array (List α) × Nat := Id.run do
  if !holds init then return (some [], #[[]], 0)
  let mut seen : Std.HashSet σ := (∅ : Std.HashSet σ).insert init
  let mut found : Array (List α) := #[[]]
  let mut frontier : Array (σ × List α) := #[(init, [])]
  let mut completed := 0
  for _ in [0:depth] do
    let mut next : Array (σ × List α) := #[]
    for (s, trace) in frontier do
      for a in actions do
        let t := step s a
        if !seen.contains t then
          seen := seen.insert t
          found := found.push (trace ++ [a])
          if !holds t then return (some (trace ++ [a]), found, completed)
          if seen.size > budget then return (none, found, completed)
          next := next.push (t, trace ++ [a])
    frontier := next
    completed := completed + 1
  return (none, found, completed)

def explore {σ α : Type} [BEq σ] [Hashable σ] (init : σ) (step : σ → α → σ) (actions : List α)
    (holds : σ → Bool) (depth budget : Nat) : Option (List α) × Nat × Nat :=
  let (violation, found, completed) := walk init step actions holds depth budget
  (violation, found.size, completed)

def traces {σ α : Type} [BEq σ] [Hashable σ] (init : σ) (step : σ → α → σ) (actions : List α)
    (depth budget : Nat) : List (List α) :=
  (walk init step actions (fun _ => true) depth budget).2.1.toList

def report {α : Type} [Repr α] (mark id : String) : Option (List α) × Nat × Nat → String
  | (some trace, _, _) => s!\"{mark} {id} falsified {reprStr trace}\"
  | (none, states, completed) => s!\"{mark} {id} bounded {completed} {states}\"

end FormalBounded";

const LASSO_HELPERS: &str = r#"namespace FormalLasso

structure Graph (σ α : Type) where
  states : Array σ
  parent : Array (Option (Nat × α))
  edges : Array (Array (α × Nat))
  layers : Nat
  complete : Bool

def build {σ α : Type} [BEq σ] [Hashable σ] (init : σ) (step : σ → α → σ) (actions : List α)
    (depth budget : Nat) : Graph σ α := Id.run do
  let mut index : Std.HashMap σ Nat := (∅ : Std.HashMap σ Nat).insert init 0
  let mut states : Array σ := #[init]
  let mut parent : Array (Option (Nat × α)) := #[none]
  let mut edges : Array (Array (α × Nat)) := #[#[]]
  let mut frontier : Array (Nat × σ) := #[(0, init)]
  let mut layers := 0
  for _ in [0:depth] do
    let mut next : Array (Nat × σ) := #[]
    for (i, s) in frontier do
      for a in actions do
        let t := step s a
        match index.get? t with
        | some j => edges := edges.modify i (·.push (a, j))
        | none =>
          if states.size > budget then
            return { states, parent, edges, layers, complete := false }
          let j := states.size
          index := index.insert t j
          states := states.push t
          parent := parent.push (some (i, a))
          edges := (edges.modify i (·.push (a, j))).push #[]
          next := next.push (j, t)
    frontier := next
    layers := layers + 1
  return { states, parent, edges, layers, complete := frontier.isEmpty }

def reach {α : Type} (edges : Array (Array (α × Nat))) (allowed : Array Bool) (sources : List Nat) :
    Array (Option (Option (Nat × α))) × Array Nat := Id.run do
  let mut seen : Array (Option (Option (Nat × α))) := Array.replicate edges.size none
  let mut queue : Array Nat := #[]
  for s in sources do
    if allowed[s]! && seen[s]!.isNone then
      seen := seen.set! s (some none)
      queue := queue.push s
  let mut head := 0
  while head < queue.size do
    let i := queue[head]!
    head := head + 1
    for (a, j) in edges[i]! do
      if allowed[j]! && seen[j]!.isNone then
        seen := seen.set! j (some (some (i, a)))
        queue := queue.push j
  return (seen, queue)

def back {α : Type} (seen : Array (Option (Option (Nat × α)))) (i : Nat) : Nat × List α := Id.run do
  let mut acc : List α := []
  let mut j := i
  for _ in [0:seen.size] do
    match seen[j]? with
    | some (some (some (k, a))) =>
      acc := a :: acc
      j := k
    | _ => break
  return (j, acc)

def components {α : Type} (edges : Array (Array (α × Nat))) (allowed : Array Bool) (roots : Array Nat) :
    Array Nat := Id.run do
  let n := edges.size
  let mut index : Array Nat := Array.replicate n n
  let mut low : Array Nat := Array.replicate n n
  let mut onStack : Array Bool := Array.replicate n false
  let mut stack : Array Nat := #[]
  let mut comp : Array Nat := Array.replicate n n
  let mut counter := 0
  let mut count := 0
  for root in roots do
    if index[root]! != n then continue
    index := index.set! root counter
    low := low.set! root counter
    counter := counter + 1
    stack := stack.push root
    onStack := onStack.set! root true
    let mut calls : Array (Nat × Nat) := #[(root, 0)]
    while !calls.isEmpty do
      let (v, e) := calls.back!
      match edges[v]![e]? with
      | some (_, w) =>
        calls := calls.set! (calls.size - 1) (v, e + 1)
        if !allowed[w]! then continue
        if index[w]! == n then
          index := index.set! w counter
          low := low.set! w counter
          counter := counter + 1
          stack := stack.push w
          onStack := onStack.set! w true
          calls := calls.push (w, 0)
        else if onStack[w]! then
          low := low.set! v (min low[v]! index[w]!)
      | none =>
        calls := calls.pop
        if let some (u, _) := calls.back? then
          low := low.set! u (min low[u]! low[v]!)
        if low[v]! == index[v]! then
          let mut more := true
          while more do
            let w := stack.back!
            stack := stack.pop
            onStack := onStack.set! w false
            comp := comp.set! w count
            more := w != v
          count := count + 1
  return comp

def search {σ α : Type} [BEq σ] [Hashable σ] [BEq α] (init : σ) (step : σ → α → σ)
    (actions fair : List α) (start : Option (σ → Bool)) (goal : σ → Bool) (depth budget : Nat) :
    Option (List α × List α) × Bool × Nat × Nat := Id.run do
  if fair.any (! actions.contains ·) then return (none, false, 0, 0)
  let g := build init step actions depth budget
  let n := g.states.size
  let good := g.states.map (! goal ·)
  let sources := match start with
    | none => [0]
    | some p =>
      let starting := g.states.map p
      (List.range n).filter fun i => starting[i]! && good[i]!
  let (seen, order) := reach g.edges good sources
  let comp := components g.edges good order
  let hops : List (α → Bool) := if fair.isEmpty then [fun _ => true] else fair.map (· == ·)
  let mut fairComp : Array Bool := Array.replicate n true
  for takes in hops do
    let mut has : Array Bool := Array.replicate n false
    for v in order do
      for (b, w) in g.edges[v]! do
        if comp[w]! == comp[v]! && takes b then
          has := has.set! comp[v]! true
    fairComp := fairComp.zipWith (· && ·) has
  let some x := order.find? (fun i => fairComp[comp[i]!]!) | return (none, g.complete, g.layers, n)
  let (s, toLoop) := back seen x
  let inside := comp.map (· == comp[x]!)
  let mut cur := x
  let mut loop : List α := []
  for takes in hops do
    let (near, around) := reach g.edges inside [cur]
    let hop := around.findSome? fun u =>
      (g.edges[u]!.find? fun (b, w) => inside[w]! && takes b).map (u, ·)
    if let some (u, (a, w)) := hop then
      loop := loop ++ (back near u).2 ++ [a]
      cur := w
  let (near, _) := reach g.edges inside [cur]
  return (some ((back (g.parent.map some) s).2 ++ toLoop, loop ++ (back near x).2), g.complete, g.layers, n)

def report {α : Type} [Repr α] (mark id : String) : Option (List α × List α) × Bool × Nat × Nat → String
  | (some (pre, loop), _, _, _) => s!"{mark} {id} lasso\x1f{reprStr pre}\x1f{reprStr loop}"
  | (none, true, layers, states) => s!"{mark} {id} bounded {layers} {states}"
  | (none, false, _, _) => s!"{mark} {id} unsettled"

end FormalLasso"#;

const SEARCH_HELPERS: &str = "namespace FormalRefute
open Plausible

scoped instance (priority := high) {n : String} {p : Prop} [h : Decidable p] :
    Decidable (NamedBinder n p) := h

scoped instance (priority := high) {α : Type u} {l : List α} {p : α → Prop} [DecidablePred p]
    {n : String} : Decidable (∀ x, NamedBinder n (x ∈ l → p x)) :=
  inferInstanceAs (Decidable (∀ x, x ∈ l → p x))

def boundedRun {α : Type u} [Repr α] {β : α → Prop} [∀ x, Testable (β x)] (var : String)
    (cfg : Configuration) (min : Bool) : (l : List α) → Gen (TestResult (∀ x, x ∈ l → β x))
  | [] => pure (.success (PSum.inr (fun _ h => nomatch h)))
  | x :: xs => do
    match ← Testable.runProp (β x) cfg min with
    | .failure h msgs n =>
      pure (.failure (fun all => h (all x List.mem_cons_self)) (s!\"{var} := {repr x}\" :: msgs) n)
    | _ =>
      match ← boundedRun var cfg min xs with
      | .failure h msgs n =>
        pure (.failure (fun all => h (fun y hy => all y (List.mem_cons_of_mem _ hy))) msgs n)
      | _ => pure (.success (PSum.inl ()))

scoped instance (priority := high) {α : Type u} [Repr α] {l : List α} {β : α → Prop}
    [∀ x, Testable (β x)] {n n' : String} :
    Testable (NamedBinder n (∀ x, NamedBinder n' (x ∈ l → β x))) where
  run cfg min := boundedRun n cfg min l

def withSamples {α : Type} [Arbitrary α] (samples : List α) : Gen α :=
  Gen.frequency Arbitrary.arbitrary
    [(1, Arbitrary.arbitrary), (1, Gen.oneOfWithDefault Arbitrary.arbitrary (samples.map pure))]

end FormalRefute";

const COUNTEREXAMPLE_MARK: &str = "Found a counter-example!";

/// A Lean file that defines the code's model and states its properties.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeanSpec {
    /// What Lean reads, which is also what the cache keys digest: the specs it
    /// imports, then the spec, under one header of their imports. The spec as it
    /// was read when it imports no spec.
    pub source: String,
    /// The namespace that holds the definitions and the properties.
    pub namespace: String,
    /// The id of each `def <name> : Prop`, as `<namespace>.<name>`, in the spec's order.
    pub properties: Vec<String>,
    /// The functions whose doc comment names the code they describe, in the spec's order.
    pub compared: Vec<Compared>,
    /// The types the spec lists samples of, as `def <Type>.samples`, in name order.
    pub sampled: Vec<String>,
    /// The state machine the spec describes with `init` and `step`, when it has one.
    pub machine: Option<Machine>,
}

/// A state machine: an `init : <State>`, a `step`, and at least one invariant or liveness
/// property.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Machine {
    /// Each `def <name> : <State> → Prop` or `def <name> (<s> : <State>) : Prop`, in the
    /// spec's order.
    pub invariants: Vec<String>,
    /// Each `inductive` and `structure` the spec defines, in the spec's order.
    pub types: Vec<String>,
    /// The actions the bounded check tries at each step. Nothing when there is neither
    /// a list of constructors nor samples.
    pub actions: Option<Actions>,
    /// How deep the bounded check explores: the spec's `depth`, or the default.
    pub depth: String,
    /// Each property written as `Temporal.leadsTo` or `Temporal.eventually` over the
    /// spec's `init` and `step`, under fairness alone, in the spec's order.
    pub liveness: Vec<Liveness>,
}

/// A liveness property the lasso check can refute.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Liveness {
    /// The property's name in the spec.
    pub name: String,
    /// The actions the property assumes fair, as the spec writes them.
    pub fair: Vec<String>,
    /// Where the property starts: `p` of `leadsTo`, nothing for `eventually`.
    pub start: Option<Predicate>,
    /// What must follow: `q` of `leadsTo`, or of `eventually`.
    pub goal: Predicate,
}

/// A state predicate a liveness property names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Predicate {
    /// A definition of the spec, by its name in the namespace.
    Named(String),
    /// A term in parentheses, as the spec writes it.
    Term(String),
}

/// Where the bounded check takes its actions from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Actions {
    /// Every constructor of the action type, none taking an argument, as a Lean list.
    /// Lean proves the list complete before the check uses it.
    Constructors(String),
    /// The spec's `<Action>.samples`.
    Samples(String),
}

impl Actions {
    fn expression(&self) -> String {
        match self {
            Self::Constructors(list) => {
                format!("(FormalBounded.complete {list} (by intro a; cases a <;> simp))")
            }
            Self::Samples(samples) => samples.clone(),
        }
    }
}

/// What the induction test found for one invariant, or for several together.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, serde::Serialize)]
pub enum Inductive {
    /// A state where the invariants hold, an action, and the state after it, where they do not.
    Broken {
        /// The state, as Lean prints it.
        state: String,
        /// The action, as Lean prints it.
        action: String,
        /// The state after the action, as Lean prints it.
        next: String,
    },
    /// The invariants held in some drawn states, and no action from them broke them.
    Kept,
}

/// The file that tests induction, and the invariants each of its tests covers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Induction {
    /// The file, ready for Lean.
    pub lean_code: String,
    /// The properties each test covers, in order: each one alone, then all of them
    /// when there is more than one.
    pub groups: Vec<Vec<String>>,
}

/// What the bounded check found for one invariant.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, serde::Serialize)]
pub enum Explored {
    /// A shortest list of actions after which the invariant does not hold.
    Falsified(String),
    /// A run the liveness property fails on: these actions, then the loop forever.
    Lasso {
        /// The actions to the loop, as Lean prints them.
        prefix: String,
        /// The actions the loop repeats, as Lean prints them.
        cycle: String,
    },
    /// A liveness property the check did not refute on a walk that missed part of the
    /// machine: cut at its depth or its state budget, or without a fair action.
    Unsettled,
    /// The invariant holds in every state reached within `depth` actions, or the
    /// liveness property holds on every reachable state.
    Bounded {
        /// How deep the check explored.
        depth: u32,
        /// How many distinct states it reached.
        states: u32,
    },
}

/// An invariant the bounded check found to hold in every state up to its depth.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, serde::Serialize)]
pub struct Bound {
    /// The property, as `<namespace>.<name>.always`.
    pub id: String,
    /// How deep the check explored.
    pub depth: u32,
    /// How many distinct states it reached.
    pub states: u32,
}

/// The file that explores a machine to a bound, and the id each of its lines answers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Exploration {
    /// The file, ready for Lean.
    pub lean_code: String,
    /// The property each exploration answers, in order.
    pub ids: Vec<String>,
}

impl Machine {
    fn runs(&self) -> bool {
        !self.invariants.is_empty()
    }

    /// What formal adds after the spec: `run`, and one property per invariant.
    fn definitions(&self, namespace: &str) -> String {
        let mut lines = vec![format!(
            "def _root_.{namespace}.run := List.foldl _root_.{namespace}.step _root_.{namespace}.init"
        )];
        lines.extend(self.invariants.iter().map(|invariant| {
            format!(
                "def _root_.{namespace}.{invariant}.{ALWAYS} : Prop := \
                 ∀ actions, _root_.{namespace}.{invariant} (_root_.{namespace}.run actions)"
            )
        }));
        lines.join("\n")
    }
}

/// A property the search found a counterexample to.
#[derive(Clone, Debug, Eq, PartialEq, serde::Deserialize, serde::Serialize)]
pub struct Refutation {
    /// The property, as `<namespace>.<name>`.
    pub id: String,
    /// The value of each variable, as Plausible prints it.
    pub counterexample: Vec<String>,
    /// What does not hold for those values.
    pub issue: String,
}

/// What Lean said on the line of one search.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Answer {
    /// Lean said nothing, because the search never ran.
    Silent,
    /// The search ran and found no counterexample.
    Unrefuted,
    /// The search found a counterexample.
    Refuted(Refutation),
}

/// The file that searches properties for a counterexample, and the line of each search.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Search {
    /// The file, ready for Lean.
    pub lean_code: String,
    /// Each property, and the line that searches it.
    pub lines: Vec<(String, u32)>,
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

fn definitions<'a>(code: &'a str, blocks: &[(String, usize, usize)]) -> HashMap<&'a str, bool> {
    definition_pattern()
        .captures_iter(code)
        .filter_map(|found| {
            Some((
                found.get(1)?.as_str(),
                in_block(blocks, found.get(0)?.start()),
            ))
        })
        .collect()
}

fn in_block(blocks: &[(String, usize, usize)], at: usize) -> bool {
    blocks
        .iter()
        .any(|(_, start, end)| *start <= at && at < *end)
}

fn init_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"(?m)^[ \t]*{DEFINITION}init\s*:\s*({IDENTIFIER})\s*(?::=|where)")
    })
}

fn declared_type_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"(?m)^[ \t]*(?:inductive|structure)\s+({IDENTIFIER})")
    })
}

fn found_in_block(pattern: &Regex, code: &str, blocks: &[(String, usize, usize)]) -> bool {
    pattern
        .find_iter(code)
        .any(|whole| in_block(blocks, whole.start()))
}

fn captured_in_block(
    pattern: &Regex,
    code: &str,
    blocks: &[(String, usize, usize)],
) -> Vec<String> {
    pattern
        .captures_iter(code)
        .filter(|found| {
            found
                .get(0)
                .is_some_and(|whole| in_block(blocks, whole.start()))
        })
        .map(|found| found[1].to_string())
        .collect()
}

fn constructors(code: &str, action: &str) -> Option<Vec<String>> {
    let header = Regex::new(&format!(
        r"(?m)^[ \t]*inductive\s+{}(?:\s+where)?[ \t]*(.*)$",
        regex::escape(action)
    ))
    .expect("the pattern is built from literals");
    let found = header.captures(code)?;
    let mut cases = found[1].to_string();
    for line in code[found.get(0)?.end()..].lines().skip(1) {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if !line.starts_with('|') {
            break;
        }
        cases.push(' ');
        cases.push_str(line);
    }
    let cases = cases.split(" deriving ").next().unwrap_or_default();
    let names: Vec<String> = cases
        .split('|')
        .map(str::trim)
        .filter(|case| !case.is_empty())
        .map(ToString::to_string)
        .collect();
    let all_plain = names.iter().all(|name| identifier_pattern().is_match(name));
    (all_plain && !names.is_empty()).then_some(names)
}

fn action_type(
    code: &str,
    blocks: &[(String, usize, usize)],
    state: &str,
    namespace: &str,
) -> Option<String> {
    let qualified = format!(r"((?:{IDENTIFIER}\.)*{IDENTIFIER})");
    let arrow = Regex::new(&format!(
        r"(?m)^[ \t]*{DEFINITION}step\s*(?:\(\s*{IDENTIFIER}\s*:\s*{state}\s*\)\s*)?:\s*(?:{state}\s*→\s*)?{qualified}\s*→\s*{state}"
    ))
    .expect("the pattern is built from literals");
    let binders = Regex::new(&format!(
        r"(?m)^[ \t]*{DEFINITION}step\s*\(\s*{IDENTIFIER}\s*:\s*{state}\s*\)\s*\(\s*{IDENTIFIER}\s*:\s*{qualified}\s*\)\s*:\s*{state}"
    ))
    .expect("the pattern is built from literals");
    let action = captured_in_block(&arrow, code, blocks)
        .into_iter()
        .chain(captured_in_block(&binders, code, blocks))
        .next()?;
    let prefix = format!("{namespace}.");
    Some(
        action
            .strip_prefix(&prefix)
            .map_or(action.clone(), ToString::to_string),
    )
}

fn depth_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        format!(r"(?m)^[ \t]*{DEFINITION}depth\s*:\s*Nat\s*:=")
    })
}

fn machine(
    code: &str,
    blocks: &[(String, usize, usize)],
    defined: &HashMap<&str, bool>,
    namespace: &str,
    stated: &[(&str, usize)],
) -> Option<Machine> {
    if defined.get("step") != Some(&true) {
        return None;
    }
    let state = captured_in_block(init_pattern(), code, blocks)
        .into_iter()
        .next()?;
    let state = regex::escape(&state);
    let actions = action_type(code, blocks, &state, namespace).and_then(|action| {
        constructors(code, &action)
            .map(|names| {
                let names: Vec<String> = names
                    .iter()
                    .map(|name| format!("{namespace}.{action}.{name}"))
                    .collect();
                Actions::Constructors(format!("[{}]", names.join(", ")))
            })
            .or_else(|| {
                (defined.get(format!("{action}.samples").as_str()) == Some(&true))
                    .then(|| Actions::Samples(format!("{namespace}.{action}.samples")))
            })
    });
    let depth = if found_in_block(depth_pattern(), code, blocks) {
        format!("{namespace}.depth")
    } else {
        DEFAULT_DEPTH.to_string()
    };
    let invariant = Regex::new(&format!(
        r"(?m)^[ \t]*{DEFINITION}({IDENTIFIER})\s*(?::\s*{state}\s*→|\(\s*{IDENTIFIER}\s*:\s*{state}\s*\)\s*:)\s*Prop\s*:="
    ))
    .expect("the pattern is built from literals");
    let invariants = captured_in_block(&invariant, code, blocks);
    let liveness: Vec<Liveness> = stated
        .iter()
        .filter_map(|(name, end)| liveness(name, declaration(code, *end), namespace))
        .collect();
    if invariants.is_empty() && liveness.is_empty() {
        return None;
    }
    Some(Machine {
        invariants,
        types: captured_in_block(declared_type_pattern(), code, blocks),
        actions,
        depth,
        liveness,
    })
}

fn declaration(code: &str, from: usize) -> &str {
    let rest = &code[from..];
    let first = rest.find('\n').map_or(rest.len(), |index| index + 1);
    let body: usize = rest[first..]
        .split_inclusive('\n')
        .take_while(|line| !ends_declaration(line))
        .map(str::len)
        .sum();
    &rest[..first + body]
}

fn ends_declaration(line: &str) -> bool {
    let line = pystr::strip(line);
    line.starts_with('#') || declaration_start_pattern().is_match(line)
}

fn declaration_start_pattern() -> &'static Regex {
    static PATTERN: OnceLock<Regex> = OnceLock::new();
    pattern(&PATTERN, || {
        r"^(?:@\[|(?:private|protected|noncomputable|partial|def|abbrev|theorem|lemma|instance|example|structure|inductive|class|namespace|section|end|open|variable|deriving|set_option|attribute|axiom|opaque|universe|mutual|notation|macro|syntax|local|scoped)\b)".to_string()
    })
}

fn arguments(text: &str) -> Option<Vec<&str>> {
    let mut found = Vec::new();
    let mut depth = 0usize;
    let mut start = None;
    for (at, c) in text.char_indices() {
        match c {
            '(' | '[' | '⟨' | '{' => {
                depth += 1;
                start.get_or_insert(at);
            }
            ')' | ']' | '⟩' | '}' => depth = depth.checked_sub(1)?,
            c if pystr::is_space(c) && depth == 0 => {
                if let Some(begin) = start.take() {
                    found.push(&text[begin..at]);
                }
            }
            _ => {
                start.get_or_insert(at);
            }
        }
    }
    if depth != 0 {
        return None;
    }
    if let Some(begin) = start {
        found.push(&text[begin..]);
    }
    Some(found)
}

fn parenthesized(argument: &str) -> Option<&str> {
    let inner = argument.strip_prefix('(')?.strip_suffix(')')?;
    (arguments(inner).is_some()).then_some(pystr::strip(inner))
}

fn fairness(assumed: &str) -> Option<Vec<String>> {
    let inner = parenthesized(assumed)?;
    if let ["Temporal.fair", action] = arguments(inner)?.as_slice() {
        return Some(vec![(*action).to_string()]);
    }
    let (binder, body) = inner.strip_prefix("fun ")?.split_once("=>")?;
    let binder = pystr::strip(binder);
    let words = arguments(body)?;
    if words == ["True"] {
        return Some(Vec::new());
    }
    words
        .split(|word| *word == "∧")
        .map(|part| match part {
            ["Temporal.fair", action, run] if *run == binder => Some((*action).to_string()),
            _ => None,
        })
        .collect()
}

fn predicate(argument: &str, namespace: &str) -> Option<Predicate> {
    if parenthesized(argument).is_some() {
        return Some(Predicate::Term(argument.to_string()));
    }
    let named = argument
        .strip_prefix(&format!("{namespace}."))
        .unwrap_or(argument);
    identifier_pattern()
        .is_match(named)
        .then(|| Predicate::Named(named.to_string()))
}

fn liveness(name: &str, body: &str, namespace: &str) -> Option<Liveness> {
    let words = arguments(body)?;
    let own = |word: &str, name: &str| word == name || word == format!("{namespace}.{name}");
    let (init, step, assumed, start, goal) = match words.as_slice() {
        ["Temporal.leadsTo", init, step, assumed, start, goal] => {
            (init, step, assumed, Some(start), goal)
        }
        ["Temporal.eventually", init, step, assumed, goal] => (init, step, assumed, None, goal),
        _ => return None,
    };
    if !own(init, "init") || !own(step, "step") {
        return None;
    }
    Some(Liveness {
        name: name.to_string(),
        fair: fairness(assumed)?,
        start: start.map_or(Some(None), |start| predicate(start, namespace).map(Some))?,
        goal: predicate(goal, namespace)?,
    })
}

fn stated_properties<'a>(
    path: &Path,
    code: &'a str,
    blocks: &[(String, usize, usize)],
) -> Result<Vec<(&'a str, usize)>, SpecError> {
    let mut stated = Vec::new();
    for found in prop_definition_pattern().captures_iter(code) {
        let whole = found.get(0).map_or(0..0, |whole| whole.range());
        let line_start = code[..whole.start].rfind('\n').map_or(0, |index| index + 1);
        let block = blocks
            .iter()
            .find(|(_, start, end)| *start <= whole.start && whole.start < *end);
        let (_, [kind, name]) = found.extract();
        let registrable = kind == "def"
            && code[line_start..whole.start].trim().is_empty()
            && identifier_pattern().is_match(name);
        match block {
            Some(_) if registrable => stated.push((name, whole.end)),
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
    Ok(stated)
}

fn sampled_types(defined: &HashMap<&str, bool>) -> Vec<String> {
    let mut types: Vec<String> = defined
        .iter()
        .filter(|(_, inside)| **inside)
        .filter_map(|(name, _)| name.strip_suffix(".samples"))
        .filter(|name| identifier_pattern().is_match(name))
        .map(ToString::to_string)
        .collect();
    types.sort();
    types
}

fn compared_functions(
    path: &Path,
    text: &str,
    namespace: &str,
    defined: &HashMap<&str, bool>,
    machine: Option<&Machine>,
) -> Result<Vec<Compared>, SpecError> {
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
        if let Some(machine) = machine.filter(|_| name == "step") {
            if machine.actions.is_none() {
                return Err(SpecError::NoReplayActions(path.to_path_buf()));
            }
            compared.push(Compared {
                function: format!("{namespace}.run"),
                code: code_line[1].to_string(),
            });
            continue;
        }
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

const SPEC_IMPORT: &str = "Spec.";

const LIBRARY_IMPORT: &str = "Formal.";

fn resolved_by_formal(module: &str) -> bool {
    module.starts_with(SPEC_IMPORT) || module.starts_with(LIBRARY_IMPORT)
}

const LIBRARIES: [(&str, &str); 1] = [("Temporal", include_str!("../lean/Temporal.lean"))];

fn imported_specs(path: &Path, text: &str) -> Result<Vec<String>, SpecError> {
    let root = path.parent().unwrap_or(path);
    let mut read = Vec::new();
    visit(root, path, text, &mut vec![path.to_path_buf()], &mut read)?;
    Ok(read.into_iter().map(|(_, text)| text).collect())
}

fn visit(
    root: &Path,
    path: &Path,
    text: &str,
    importing: &mut Vec<PathBuf>,
    read: &mut Vec<(PathBuf, String)>,
) -> Result<(), SpecError> {
    for import in imports(text.trim_start_matches('\u{feff}')) {
        let library = import.module.strip_prefix(LIBRARY_IMPORT);
        let imported = match (library, import.module.strip_prefix(SPEC_IMPORT)) {
            (Some(name), _) => PathBuf::from(format!("<formal>/{name}.lean")),
            (None, Some(name)) => root.join(format!("{}.lean", name.replace('.', "/"))),
            (None, None) => continue,
        };
        if read.iter().any(|(done, _)| *done == imported) {
            continue;
        }
        if let Some(name) = library {
            let Some((_, library_text)) = LIBRARIES.iter().find(|(known, _)| *known == name) else {
                let known: Vec<String> = LIBRARIES
                    .iter()
                    .map(|(known, _)| format!("`{LIBRARY_IMPORT}{known}`"))
                    .collect();
                return Err(SpecError::NoSuchLibrary {
                    spec: path.to_path_buf(),
                    import: import.module.clone(),
                    known: known.join(", "),
                });
            };
            read.push((imported, (*library_text).to_string()));
            continue;
        }
        if let Some(start) = importing.iter().position(|seen| *seen == imported) {
            let chain: Vec<String> = importing[start..]
                .iter()
                .chain(std::iter::once(&imported))
                .map(|step| step.display().to_string())
                .collect();
            return Err(SpecError::ImportCycle {
                chain: chain.join(" → "),
            });
        }
        let imported_text = fs::read_to_string(&imported).map_err(|_| SpecError::NoSuchImport {
            spec: path.to_path_buf(),
            import: import.module.clone(),
            path: imported.clone(),
        })?;
        if let Some(found) = runs_code(&imported_text) {
            return Err(SpecError::RunsCode {
                path: imported,
                found,
            });
        }
        importing.push(imported.clone());
        visit(root, &imported, &imported_text, importing, read)?;
        importing.pop();
        read.push((imported, imported_text));
    }
    Ok(())
}

fn source(text: String, imported: &[String]) -> String {
    if imported.is_empty() {
        return text;
    }
    let files: Vec<&str> = imported
        .iter()
        .map(String::as_str)
        .chain(std::iter::once(text.as_str()))
        .map(|file| file.trim_start_matches('\u{feff}'))
        .collect();
    let modules: Vec<String> = files
        .iter()
        .flat_map(|file| imports(file))
        .map(|import| import.module)
        .filter(|module| !resolved_by_formal(module))
        .collect();
    let mut lines = import_lines(modules.iter().map(String::as_str));
    lines.extend(files.iter().map(|file| blanked(file, &imports(file))));
    format!("{}\n", lines.join("\n"))
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

fn search_of(id: &str) -> String {
    format!("open FormalRefute in example : _root_.{id} := by unfold _root_.{id}; plausible")
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

        let stated = stated_properties(path, &code, &blocks)?;
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
        let mut properties: Vec<String> = stated
            .iter()
            .map(|(name, _)| format!("{namespace}.{name}"))
            .collect();
        let defined = definitions(&code, &blocks);
        let machine = machine(&code, &blocks, &defined, &namespace, &stated);
        let running = machine.as_ref().filter(|machine| machine.runs());
        if let Some(machine) = running {
            if defined.contains_key("run") {
                return Err(SpecError::MachineRun(path.to_path_buf()));
            }
            properties.extend(
                machine
                    .invariants
                    .iter()
                    .map(|invariant| format!("{namespace}.{invariant}.{ALWAYS}")),
            );
        }
        if properties.is_empty() {
            return Err(SpecError::NoLeanProperties(path.to_path_buf()));
        }
        let compared = compared_functions(path, &text, &namespace, &defined, running)?;
        let sampled = sampled_types(&defined);
        let imported = imported_specs(path, &text)?;
        let mut source = source(text, &imported);
        if let Some(machine) = running {
            source.push('\n');
            source.push_str(&machine.definitions(&namespace));
            source.push('\n');
        }
        Ok(Self {
            source,
            namespace,
            properties,
            compared,
            sampled,
            machine,
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

    /// Where the proof of a property lives under `root`: `<root>/<Namespace>/<name>.lean`.
    #[must_use]
    pub fn proof_path(&self, root: &Path, id: &str) -> PathBuf {
        let name = id
            .strip_prefix(&format!("{}.", self.namespace))
            .unwrap_or(id);
        root.join(&self.namespace).join(format!("{name}.lean"))
    }

    /// The cache key of a property, which covers the whole spec.
    #[must_use]
    pub fn key(&self, id: &str) -> String {
        lean_spec_key(&self.source, id)
    }

    /// The cache key of the spec's answers for a compared function.
    #[must_use]
    pub fn answers_key(&self, function: &str) -> String {
        let command = std::iter::once(evaluation_of(function))
            .chain(self.replay_lines(function))
            .collect::<Vec<_>>()
            .join("\n");
        lean_spec_answers_key(&self.source, ENCODING, &command)
    }

    fn replay_lines(&self, function: &str) -> Vec<String> {
        let namespace = &self.namespace;
        let Some((machine, actions)) = self
            .explored()
            .filter(|(machine, _)| machine.runs() && function == format!("{namespace}.run"))
        else {
            return Vec::new();
        };
        let mut lines = vec![EXPLORATION_HELPERS.to_string()];
        lines.extend(self.deriving(
            Some(machine),
            &["BEq", "Hashable", "Lean.ToJson"],
            "open FormalCompare in ",
        ));
        lines.push(format!(
            "def _root_.{namespace}.run.inputs := FormalBounded.traces {namespace}.init {namespace}.step {} {} {STATE_BUDGET}",
            actions.expression(),
            machine.depth
        ));
        lines
    }

    /// The file that prints the inputs of each function in `functions`, and the spec's answers.
    ///
    /// Each function prints one line: [`COMPARE_MARK`], the function, and a JSON
    /// list of `[input, answer]` pairs.
    #[must_use]
    pub fn evaluation(&self, functions: &[&str]) -> String {
        let spec = self.source.trim_start_matches('\u{feff}');
        let spec_imports = imports(spec);
        let replay: Vec<String> = functions
            .iter()
            .flat_map(|function| self.replay_lines(function))
            .collect();
        let extra = (!replay.is_empty()).then_some(EXPLORATION_IMPORT);
        let mut lines = import_lines(
            std::iter::once(EVALUATION_IMPORT)
                .chain(extra)
                .chain(spec_imports.iter().map(|import| import.module.as_str())),
        );
        lines.push(blanked(spec, &spec_imports));
        lines.push(ENCODING.to_string());
        lines.extend(replay);
        lines.extend(functions.iter().map(|function| evaluation_of(function)));
        format!("{}\n", lines.join("\n"))
    }

    /// The cache key of the search for a counterexample to the property `id`.
    #[must_use]
    pub fn search_key(&self, id: &str) -> String {
        let helpers = std::iter::once(SEARCH_HELPERS.to_string())
            .chain(self.derived())
            .collect::<Vec<_>>()
            .join("\n");
        lean_spec_search_key(&self.source, &helpers, &self.search_line(id))
    }

    fn search_line(&self, id: &str) -> String {
        match self.invariant_of(id) {
            Some(invariant) => format!(
                "open FormalRefute in example : _root_.{id} := by \
                 unfold _root_.{id} _root_.{}.{invariant}; plausible",
                self.namespace
            ),
            None => search_of(id),
        }
    }

    fn deriving(&self, machine: Option<&Machine>, classes: &[&str], scope: &str) -> Vec<String> {
        let namespace = &self.namespace;
        machine
            .into_iter()
            .flat_map(|machine| &machine.types)
            .flat_map(|declared| {
                classes.iter().map(move |class| {
                    format!("{scope}deriving instance {class} for {namespace}.{declared}")
                })
            })
            .collect()
    }

    fn derived(&self) -> Vec<String> {
        self.deriving(
            self.machine.as_ref().filter(|machine| machine.runs()),
            &["Repr", "Plausible.Shrinkable", "Plausible.Arbitrary"],
            "",
        )
    }

    fn exploration_of(&self, machine: &Machine, actions: &Actions, invariant: &str) -> String {
        let namespace = &self.namespace;
        let depth = &machine.depth;
        let (instance, decided) = self.decision(invariant);
        format!(
            "{instance}\n\
             #eval IO.println (FormalBounded.report \"{EXPLORATION_MARK}\" \"{namespace}.{invariant}.{ALWAYS}\" \
             (FormalBounded.explore {namespace}.init {namespace}.step {} {decided} {depth} {STATE_BUDGET}))",
            actions.expression()
        )
    }

    fn decision(&self, name: &str) -> (String, String) {
        (
            self.decidable(name),
            format!("(fun s => decide ({}.{name} s))", self.namespace),
        )
    }

    fn decidable(&self, invariant: &str) -> String {
        let namespace = &self.namespace;
        format!(
            "instance : DecidablePred {namespace}.{invariant} := fun s => by unfold {namespace}.{invariant}; infer_instance"
        )
    }

    fn explored(&self) -> Option<(&Machine, &Actions)> {
        let machine = self.machine.as_ref()?;
        Some((machine, machine.actions.as_ref()?))
    }

    fn exploration_helpers(&self) -> Vec<String> {
        [EXPLORATION_HELPERS, LASSO_HELPERS]
            .into_iter()
            .map(ToString::to_string)
            .chain(self.deriving(self.machine.as_ref(), &["Repr", "BEq", "Hashable"], ""))
            .collect()
    }

    fn lasso_of(&self, machine: &Machine, actions: &Actions, liveness: &Liveness) -> String {
        let namespace = &self.namespace;
        let mut lines = Vec::new();
        let mut decision = |predicate: &Predicate| match predicate {
            Predicate::Term(term) => format!("(fun s => decide ({term} s))"),
            Predicate::Named(name) => {
                let (instance, decided) = self.decision(name);
                lines.push(instance);
                decided
            }
        };
        let start = liveness.start.as_ref().map_or_else(
            || "none".to_string(),
            |start| format!("(some {})", decision(start)),
        );
        let goal = decision(&liveness.goal);
        lines.push(format!(
            "namespace {namespace}\n#eval IO.println (FormalLasso.report \"{EXPLORATION_MARK}\" \"{namespace}.{}\" \
             (FormalLasso.search {namespace}.init {namespace}.step {} [{}] {start} {goal} {} {STATE_BUDGET}))\nend {namespace}",
            liveness.name,
            actions.expression(),
            liveness.fair.join(", "),
            machine.depth
        ));
        lines.join("\n")
    }

    fn liveness_of(&self, id: &str) -> Option<&Liveness> {
        let name = id.strip_prefix(&format!("{}.", self.namespace))?;
        self.machine
            .as_ref()?
            .liveness
            .iter()
            .find(|liveness| liveness.name == name)
    }

    fn exploration_line(&self, id: &str) -> Option<String> {
        let (machine, actions) = self.explored()?;
        if let Some(invariant) = self.invariant_of(id) {
            return Some(self.exploration_of(machine, actions, invariant));
        }
        Some(self.lasso_of(machine, actions, self.liveness_of(id)?))
    }

    /// The cache key of the bounded check of the property `id`.
    #[must_use]
    pub fn exploration_key(&self, id: &str) -> String {
        let line = self.exploration_line(id).unwrap_or_default();
        let helpers = self.exploration_helpers().join("\n");
        lean_spec_search_key(&self.source, &helpers, &format!("bounded:{line}"))
    }

    fn invariant_of<'a>(&self, id: &'a str) -> Option<&'a str> {
        id.strip_prefix(&format!("{}.", self.namespace))
            .and_then(|name| name.strip_suffix(&format!(".{ALWAYS}")))
            .filter(|name| {
                self.machine.as_ref().is_some_and(|machine| {
                    machine.invariants.iter().any(|invariant| invariant == name)
                })
            })
    }

    /// The properties the bounded check can explore, those of a machine whose actions
    /// are known: each invariant, then each liveness property.
    #[must_use]
    pub fn explorable(&self) -> Vec<String> {
        self.explored()
            .map(|(machine, _)| {
                let namespace = &self.namespace;
                machine
                    .invariants
                    .iter()
                    .map(|invariant| format!("{namespace}.{invariant}.{ALWAYS}"))
                    .chain(
                        machine
                            .liveness
                            .iter()
                            .map(|liveness| format!("{namespace}.{}", liveness.name)),
                    )
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The file that explores the machine to its depth, once for each property in `ids`.
    #[must_use]
    pub fn exploration(&self, ids: &[&str]) -> Exploration {
        let spec = self.source.trim_start_matches('\u{feff}');
        let spec_imports = imports(spec);
        let mut lines = import_lines(
            std::iter::once(EXPLORATION_IMPORT)
                .chain(spec_imports.iter().map(|import| import.module.as_str())),
        );
        lines.push(blanked(spec, &spec_imports));
        lines.extend(self.exploration_helpers());
        let mut explored = Vec::new();
        for id in ids {
            if let Some(line) = self.exploration_line(id) {
                lines.push(line);
                explored.push((*id).to_string());
            }
        }
        Exploration {
            lean_code: format!("{}\n", lines.join("\n")),
            ids: explored,
        }
    }

    fn plausible_prelude(&self, extra: Option<&str>) -> Vec<String> {
        let spec = self.source.trim_start_matches('\u{feff}');
        let spec_imports = imports(spec);
        let mut lines = import_lines(
            std::iter::once(SEARCH_IMPORT)
                .chain(extra)
                .chain(spec_imports.iter().map(|import| import.module.as_str())),
        );
        lines.extend(blanked(spec, &spec_imports).split('\n').map(str::to_string));
        lines.extend(SEARCH_HELPERS.split('\n').map(str::to_string));
        let namespace = &self.namespace;
        lines.extend(self.derived());
        lines.extend(self.sampled.iter().map(|sampled| {
            format!(
                "open {namespace} in instance (priority := high) : Plausible.Arbitrary {sampled} := \
                 ⟨FormalRefute.withSamples {namespace}.{sampled}.samples⟩"
            )
        }));
        lines
    }

    fn induction_of(&self, actions: &Actions, invariants: &[&str], key: &str) -> String {
        let namespace = &self.namespace;
        let holds: Vec<String> = invariants
            .iter()
            .map(|invariant| format!("decide ({namespace}.{invariant} s)"))
            .collect();
        format!(
            "#eval do IO.println (FormalInductive.report \"{INDUCTION_MARK}\" \"{key}\" \
             (← FormalInductive.search Plausible.Arbitrary.arbitrary {namespace}.step {} \
             (fun s => {}) {INDUCTION_TRIES}))",
            actions.expression(),
            holds.join(" && ")
        )
    }

    /// The cache key of the induction test of `ids`, alone or together.
    #[must_use]
    pub fn induction_key(&self, ids: &[&str]) -> String {
        let invariants: Vec<&str> = ids.iter().filter_map(|id| self.invariant_of(id)).collect();
        let line = self
            .explored()
            .map(|(_, actions)| self.induction_of(actions, &invariants, &ids.join(",")))
            .unwrap_or_default();
        lean_spec_search_key(
            &self.source,
            &format!(
                "{SEARCH_HELPERS}\n{EXPLORATION_HELPERS}\n{INDUCTION_HELPERS}\n{}",
                self.derived().join("\n")
            ),
            &format!("inductive:{line}"),
        )
    }

    /// The file that tests whether each invariant in `ids` is kept by every step, then
    /// whether all of them are kept together.
    #[must_use]
    pub fn induction(&self, ids: &[&str]) -> Induction {
        let mut lines = self.plausible_prelude(Some(EXPLORATION_IMPORT));
        lines.push(EXPLORATION_HELPERS.to_string());
        lines.push(INDUCTION_HELPERS.to_string());
        let mut groups = Vec::new();
        if let Some((_, actions)) = self.explored() {
            let tested: Vec<(&str, &str)> = ids
                .iter()
                .filter_map(|id| Some((*id, self.invariant_of(id)?)))
                .collect();
            lines.extend(
                tested
                    .iter()
                    .map(|(_, invariant)| self.decidable(invariant)),
            );
            for (id, invariant) in &tested {
                lines.push(self.induction_of(actions, &[invariant], id));
                groups.push(vec![(*id).to_string()]);
            }
            if tested.len() > 1 {
                let all: Vec<String> = tested.iter().map(|(id, _)| (*id).to_string()).collect();
                let invariants: Vec<&str> =
                    tested.iter().map(|(_, invariant)| *invariant).collect();
                lines.push(self.induction_of(actions, &invariants, &all.join(",")));
                groups.push(all);
            }
        }
        Induction {
            lean_code: format!("{}\n", lines.join("\n")),
            groups,
        }
    }

    /// The file that searches each property in `ids` for a counterexample.
    ///
    /// The values of a type the spec lists samples of are drawn half from
    /// those samples. Each search is one line, and Lean answers it on that line.
    #[must_use]
    pub fn search(&self, ids: &[&str]) -> Search {
        let mut lines = self.plausible_prelude(None);
        let mut searched = Vec::new();
        for id in ids {
            lines.push(self.search_line(id));
            searched.push((
                (*id).to_string(),
                u32::try_from(lines.len()).unwrap_or(u32::MAX),
            ));
        }
        Search {
            lean_code: format!("{}\n", lines.join("\n")),
            lines: searched,
        }
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
        let spec = self.source.trim_start_matches('\u{feff}');
        let proof = proof.trim_start_matches('\u{feff}');
        let spec_imports = imports(spec);
        let proof_imports = imports(proof);

        let mut lines = import_lines(
            spec_imports
                .iter()
                .chain(&proof_imports)
                .map(|import| import.module.as_str())
                .filter(|module| !resolved_by_formal(module)),
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

/// What the induction test printed for each group of `induction`, in order.
///
/// A group is left out when Lean printed nothing for it, or when no drawn state
/// satisfied it, so nothing was tested.
#[must_use]
pub fn read_induction(induction: &Induction, printed: &[&str]) -> Vec<(Vec<String>, Inductive)> {
    induction
        .groups
        .iter()
        .filter_map(|group| {
            let mark = format!("{INDUCTION_MARK} {} ", group.join(","));
            let line = printed
                .iter()
                .find_map(|line| line.strip_prefix(&mark))?
                .trim_end();
            let found = if let Some(held) = line.strip_prefix("kept ") {
                if held.parse::<u32>().ok()? == 0 {
                    return None;
                }
                Inductive::Kept
            } else {
                let mut parts = line.strip_prefix("broken\u{1f}")?.split('\u{1f}');
                Inductive::Broken {
                    state: parts.next()?.to_string(),
                    action: parts.next()?.to_string(),
                    next: parts.next()?.to_string(),
                }
            };
            Some((group.clone(), found))
        })
        .collect()
}

/// What the bounded check printed for each property of `exploration`, in order.
///
/// A property is left out when Lean printed nothing for it: its invariant was
/// not decidable, or Lean never ran.
#[must_use]
pub fn read_exploration(exploration: &Exploration, printed: &[&str]) -> Vec<(String, Explored)> {
    exploration
        .ids
        .iter()
        .filter_map(|id| {
            let mark = format!("{EXPLORATION_MARK} {id} ");
            let line = printed
                .iter()
                .find_map(|line| line.strip_prefix(mark.as_str()))?;
            let line = line.trim_end();
            let explored = if let Some(trace) = line.strip_prefix("falsified ") {
                Explored::Falsified(trace.to_string())
            } else if let Some(lasso) = line.strip_prefix("lasso\u{1f}") {
                let (prefix, cycle) = lasso.split_once('\u{1f}')?;
                Explored::Lasso {
                    prefix: prefix.to_string(),
                    cycle: cycle.to_string(),
                }
            } else if line == "unsettled" {
                Explored::Unsettled
            } else {
                let mut words = line.strip_prefix("bounded ")?.split(' ');
                Explored::Bounded {
                    depth: words.next()?.parse().ok()?,
                    states: words.next()?.parse().ok()?,
                }
            };
            Some((id.clone(), explored))
        })
        .collect()
}

/// What Lean said on each line of `search`, one answer per line, in order.
#[must_use]
pub fn read_search(search: &Search, said: &[(u32, String)]) -> Vec<Answer> {
    search
        .lines
        .iter()
        .map(|(id, line)| {
            let mut on_line = said.iter().filter(|(at, _)| at == line).peekable();
            if on_line.peek().is_none() {
                return Answer::Silent;
            }
            on_line
                .find_map(|(_, data)| refutation(id, data))
                .map_or(Answer::Unrefuted, Answer::Refuted)
        })
        .collect()
}

fn refutation(id: &str, data: &str) -> Option<Refutation> {
    let (_, found) = data.split_once(COUNTEREXAMPLE_MARK)?;
    let mut entries: Vec<String> = Vec::new();
    for line in found.split('\n').filter(|line| !line.is_empty()) {
        if line.starts_with('(') || line.starts_with('-') {
            break;
        }
        match entries.last_mut() {
            Some(entry) if line.starts_with(' ') => {
                entry.push('\n');
                entry.push_str(line);
            }
            _ => entries.push(line.to_string()),
        }
    }
    let issue = entries
        .iter()
        .find_map(|entry| entry.strip_prefix("issue: "))?;
    Some(Refutation {
        id: id.to_string(),
        counterexample: entries
            .iter()
            .filter(|entry| !entry.starts_with("issue: ") && !entry.starts_with("guard:"))
            .cloned()
            .collect(),
        issue: issue.to_string(),
    })
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

    use tempfile::TempDir;

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
    fn a_proof_lives_under_its_namespace_by_the_name_after_it() {
        assert_eq!(
            demo().proof_path(Path::new("proofs"), "Demo.double_even"),
            PathBuf::from("proofs/Demo/double_even.lean")
        );
        assert_eq!(
            demo().proof_path(Path::new("proofs"), "Demo.inv.always"),
            PathBuf::from("proofs/Demo/inv.always.lean")
        );
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
            function_code: spec.source.clone(),
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
    fn a_type_with_samples_inside_the_namespace_is_sampled() {
        let spec = with("def Char.samples : List Char := ['a']\ndef Nat.samples : List Nat := [0]")
            .expect("it parses");
        assert_eq!(spec.sampled, ["Char", "Nat"]);
        assert_eq!(
            parse(&format!("def Char.samples : List Char := ['a']\n{DEMO}"))
                .expect("it parses")
                .sampled,
            Vec::<String>::new()
        );
    }

    #[test]
    fn the_search_draws_from_the_samples_and_gives_each_property_its_own_line() {
        let spec = with("def Char.samples : List Char := ['a']").expect("it parses");
        let search = spec.search(&["Demo.double_even", "Demo.double_mono"]);
        let lines: Vec<&str> = search.lean_code.split('\n').collect();
        assert_eq!(lines[0], "import Plausible");
        assert!(search.lean_code.contains(
            "open Demo in instance (priority := high) : Plausible.Arbitrary Char := ⟨FormalRefute.withSamples Demo.Char.samples⟩"
        ));
        for (id, line) in &search.lines {
            let at = usize::try_from(*line).expect("it fits") - 1;
            assert_eq!(
                lines[at],
                format!(
                    "open FormalRefute in example : _root_.{id} := by unfold _root_.{id}; plausible"
                )
            );
        }
    }

    const SEARCHED: &str = "namespace Demo\n\ndef double (n : Nat) : Nat := n + n\n\ndef double_odd : Prop := ∀ n, double n % 2 = 1\n\ndef double_mono : Prop := ∀ a b, a ≤ b → double a ≤ double b\n\ndef Char.samples : List Char := ['\\u2028']\n\ndef space_free : Prop := ∀ s : List Char, ∀ c ∈ s, c.toNat < 128\n\nend Demo\n";

    #[test]
    fn what_lean_said_on_a_search_line_is_read_as_a_refutation_or_as_nothing_found() {
        let spec = parse(SEARCHED).expect("it parses");
        let search = spec.search(&["Demo.double_odd", "Demo.double_mono", "Demo.space_free"]);
        let line = |at: usize| search.lines[at].1;
        let said = [
            (
                line(0),
                "\n===================\nFound a counter-example!\nn := 0\nissue: 0 = 1 does not hold\n(0 shrinks)\n-------------------".to_string(),
            ),
            (line(1), "Unable to find a counter-example".to_string()),
            (line(1), "declaration uses `sorry`".to_string()),
            (
                line(2),
                "\n===================\nFound a counter-example!\ns := ['\u{2028}']\nc := '\u{2028}'\nissue: 8232 < 128 does not hold\n(5 shrinks)\n-------------------".to_string(),
            ),
        ];
        let refutation = |id: &str, counterexample: &[&str], issue: &str| {
            Answer::Refuted(Refutation {
                id: id.to_string(),
                counterexample: counterexample.iter().map(ToString::to_string).collect(),
                issue: issue.to_string(),
            })
        };
        assert_eq!(
            read_search(&search, &said),
            [
                refutation("Demo.double_odd", &["n := 0"], "0 = 1 does not hold"),
                Answer::Unrefuted,
                refutation(
                    "Demo.space_free",
                    &["s := ['\u{2028}']", "c := '\u{2028}'"],
                    "8232 < 128 does not hold"
                ),
            ]
        );
        assert_eq!(
            read_search(&search, &said[1..3]),
            [Answer::Silent, Answer::Unrefuted, Answer::Silent]
        );
    }

    #[test]
    fn a_value_lean_wraps_over_several_lines_stays_one_value() {
        let spec = demo();
        let search = spec.search(&["Demo.double_even"]);
        let line = search.lines[0].1;
        let found = "\n===================\nFound a counter-example!\ns := [0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0]\nissue: 45 < 45 does not hold\n(211 shrinks)\n-------------------";
        let read = read_search(&search, &[(line, found.to_string())]);
        let [Answer::Refuted(refutation)] = read.as_slice() else {
            panic!("one refutation, got {read:?}");
        };
        assert_eq!(
            refutation.counterexample,
            [
                "s := [0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0,\n 0]"
            ]
        );
        assert_eq!(refutation.issue, "45 < 45 does not hold");
    }

    const COUNTER: &str = "namespace Counter\n\ninductive Action where\n  | inc\n  | reset\n\nstructure State where\n  count : Nat\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .inc => ⟨s.count + 1⟩\n  | .reset => ⟨0⟩\n\ndef count_below_three : State → Prop := fun s => s.count < 3\n\ndef init_is_zero : Prop := init.count = 0\n\nend Counter\n";

    #[test]
    fn an_init_and_a_step_make_a_machine_and_each_invariant_a_property() {
        let spec = parse(COUNTER).expect("it parses");
        assert_eq!(
            spec.machine,
            Some(Machine {
                invariants: vec!["count_below_three".to_string()],
                types: vec!["Action".to_string(), "State".to_string()],
                actions: Some(Actions::Constructors(
                    "[Counter.Action.inc, Counter.Action.reset]".to_string()
                )),
                depth: "10".to_string(),
                liveness: Vec::new(),
            })
        );
        assert_eq!(
            spec.properties,
            ["Counter.init_is_zero", "Counter.count_below_three.always"]
        );
        assert!(
            spec.source.ends_with(
                "def _root_.Counter.run := List.foldl _root_.Counter.step _root_.Counter.init\ndef _root_.Counter.count_below_three.always : Prop := ∀ actions, _root_.Counter.count_below_three (_root_.Counter.run actions)\n"
            ),
            "{}",
            spec.source
        );
        assert_eq!(demo().machine, None);
        assert!(!demo().source.contains("def run"));
    }

    #[test]
    fn a_machine_whose_invariants_are_its_only_properties_is_a_spec() {
        let spec = parse(&COUNTER.replace("def init_is_zero : Prop := init.count = 0\n", ""))
            .expect("it parses");
        assert_eq!(spec.properties, ["Counter.count_below_three.always"]);
    }

    #[test]
    fn a_machine_in_an_unclosed_namespace_still_names_its_properties_from_the_root() {
        let spec = parse(&COUNTER.replace("\nend Counter\n", "\n")).expect("it parses");
        assert!(
            spec.source.contains(
                "def _root_.Counter.count_below_three.always : Prop := ∀ actions, _root_.Counter.count_below_three (_root_.Counter.run actions)"
            ),
            "{}",
            spec.source
        );
    }

    #[test]
    fn an_init_and_a_step_without_an_invariant_are_no_machine() {
        let text = "namespace Old\n\ndef init : Nat := 0\n\ndef step (n : Nat) : Nat := n + 1\n\ndef run : Nat := 1\n\ndef step_grows : Prop := ∀ n, n < step n\n\nend Old\n";
        let spec = parse(text).expect("it parses");
        assert_eq!(spec.machine, None);
        assert_eq!(spec.properties, ["Old.step_grows"]);
        assert_eq!(spec.source, text);
    }

    #[test]
    fn an_invariant_may_take_its_state_as_a_binder_and_carry_attributes() {
        let spec = parse(
            &COUNTER
                .replace(
                    "def count_below_three : State → Prop := fun s => s.count < 3",
                    "@[simp] def count_below_three (s : State) : Prop := s.count < 3",
                )
                .replace("def init : State := ⟨0⟩", "abbrev init : State := ⟨0⟩"),
        )
        .expect("it parses");
        assert_eq!(
            spec.properties,
            ["Counter.init_is_zero", "Counter.count_below_three.always"]
        );
    }

    #[test]
    fn actions_with_arguments_come_from_samples_and_a_spec_may_set_the_depth() {
        let with_samples = parse(
            &COUNTER
                .replace("  | inc\n", "  | add (n : Nat)\n")
                .replace("  | .inc => ⟨s.count + 1⟩", "  | .add n => ⟨s.count + n⟩")
                .replace(
                    "end Counter",
                    "def Action.samples : List Action := [.add 1, .reset]\n\ndef depth : Nat := 4\n\nend Counter",
                ),
        )
        .expect("it parses");
        let machine = with_samples.machine.expect("a machine");
        assert_eq!(
            machine.actions,
            Some(Actions::Samples("Counter.Action.samples".to_string()))
        );
        assert_eq!(machine.depth, "Counter.depth");
        let without = parse(
            &COUNTER
                .replace("  | inc\n", "  | add (n : Nat)\n")
                .replace("  | .inc => ⟨s.count + 1⟩", "  | .add n => ⟨s.count + n⟩"),
        )
        .expect("it parses");
        assert_eq!(without.machine.as_ref().expect("a machine").actions, None);
        assert_eq!(without.explorable(), Vec::<String>::new());
    }

    #[test]
    fn every_constructor_counts_across_blank_lines_comments_and_one_line_headers() {
        let with_jump = |actions: &str| {
            parse(
                &COUNTER
                    .replace("inductive Action where\n  | inc\n  | reset\n", actions)
                    .replace("  | .reset => ⟨0⟩", "  | .reset => ⟨0⟩\n  | .jump => ⟨5⟩"),
            )
            .expect("it parses")
            .machine
            .expect("a machine")
            .actions
        };
        let all = Some(Actions::Constructors(
            "[Counter.Action.inc, Counter.Action.reset, Counter.Action.jump]".to_string(),
        ));
        for actions in [
            "inductive Action where\n  | inc\n  | reset\n\n  | jump\n",
            "inductive Action where\n  | inc\n  | reset\n  -- the jump\n  | jump\n",
            "inductive Action where\n  | inc\n  | reset\n  /-- the jump -/\n  | jump\n",
            "inductive Action where | inc | reset | jump\n",
            "inductive Action\n  | inc\n  | reset\n  | jump\n  deriving Repr\n",
        ] {
            assert_eq!(with_jump(actions), all, "{actions}");
        }
    }

    #[test]
    fn a_step_with_two_binders_or_a_qualified_action_names_its_actions() {
        for step in [
            "def step (s : State) (a : Action) : State :=\n  match a with",
            "def step (s : State) : Counter.Action → State",
            "def step : State → Action → State",
        ] {
            let spec = parse(&COUNTER.replace("def step (s : State) : Action → State", step))
                .expect("it parses");
            assert_eq!(
                spec.machine.expect("a machine").actions,
                Some(Actions::Constructors(
                    "[Counter.Action.inc, Counter.Action.reset]".to_string()
                )),
                "{step}"
            );
        }
    }

    #[test]
    fn only_a_depth_of_type_nat_is_the_depth() {
        let helper = parse(&COUNTER.replace(
            "end Counter",
            "def depth (s : State) : Nat := s.count\n\nend Counter",
        ))
        .expect("it parses");
        assert_eq!(helper.machine.expect("a machine").depth, "10");
        let set = parse(&COUNTER.replace("end Counter", "def depth : Nat := 4\n\nend Counter"))
            .expect("it parses");
        assert_eq!(set.machine.expect("a machine").depth, "Counter.depth");
    }

    #[test]
    fn the_exploration_walks_the_machine_once_per_invariant_and_reads_back() {
        let spec = parse(COUNTER).expect("it parses");
        assert_eq!(spec.explorable(), ["Counter.count_below_three.always"]);
        let exploration =
            spec.exploration(&["Counter.count_below_three.always", "Counter.init_is_zero"]);
        assert_eq!(exploration.ids, ["Counter.count_below_three.always"]);
        assert!(
            exploration
                .lean_code
                .starts_with("import Std.Data.HashSet\n")
        );
        assert!(
            exploration
                .lean_code
                .contains("deriving instance Hashable for Counter.State")
        );
        assert!(exploration.lean_code.contains(
            "(FormalBounded.explore Counter.init Counter.step (FormalBounded.complete [Counter.Action.inc, Counter.Action.reset] (by intro a; cases a <;> simp)) (fun s => decide (Counter.count_below_three s)) 10 100000))"
        ));
        let read = read_exploration(
            &exploration,
            &[
                "formal-bounded Counter.count_below_three.always falsified [Counter.Action.inc, Counter.Action.inc, Counter.Action.inc]\n",
            ],
        );
        assert_eq!(
            read,
            [(
                "Counter.count_below_three.always".to_string(),
                Explored::Falsified(
                    "[Counter.Action.inc, Counter.Action.inc, Counter.Action.inc]".to_string()
                )
            )]
        );
        let bounded = read_exploration(
            &exploration,
            &["formal-bounded Counter.count_below_three.always bounded 10 3\n"],
        );
        assert_eq!(
            bounded[0].1,
            Explored::Bounded {
                depth: 10,
                states: 3
            }
        );
        assert_eq!(read_exploration(&exploration, &[]), []);
    }

    #[test]
    fn a_code_line_on_step_replays_the_machine_as_run() {
        let spec = parse(&COUNTER.replace(
            "def step (s : State) : Action → State",
            "/-- code: src/counter.rs step -/\ndef step (s : State) : Action → State",
        ))
        .expect("it parses");
        assert_eq!(
            spec.compared,
            [Compared {
                function: "Counter.run".to_string(),
                code: "src/counter.rs step".to_string(),
            }]
        );
        let evaluation = spec.evaluation(&["Counter.run"]);
        assert!(evaluation.starts_with("import Lean.Data.Json\nimport Std.Data.HashSet\n"));
        assert!(
            evaluation
                .contains("open FormalCompare in deriving instance Lean.ToJson for Counter.Action")
        );
        assert!(evaluation.contains(
            "def _root_.Counter.run.inputs := FormalBounded.traces Counter.init Counter.step (FormalBounded.complete [Counter.Action.inc, Counter.Action.reset] (by intro a; cases a <;> simp)) 10 100000"
        ));
        assert_ne!(
            spec.answers_key("Counter.run"),
            parse(COUNTER)
                .expect("it parses")
                .answers_key("Counter.run")
        );
        let unlisted = parse(
            &COUNTER
                .replace(
                    "def step (s : State) : Action → State",
                    "/-- code: src/counter.rs step -/\ndef step (s : State) : Action → State",
                )
                .replace("  | inc\n", "  | add (n : Nat)\n")
                .replace("  | .inc => ⟨s.count + 1⟩", "  | .add n => ⟨s.count + n⟩"),
        );
        assert!(
            matches!(unlisted, Err(SpecError::NoReplayActions(_))),
            "{unlisted:?}"
        );
    }

    const CYCLE: &str = "namespace Cycle\n\ninductive Action where\n  | inc\n  | reset\n\nstructure State where\n  count : Nat\n\ndef init : State := ⟨0⟩\n\ndef step (s : State) : Action → State\n  | .inc => ⟨if s.count = 2 then 0 else s.count + 1⟩\n  | .reset => ⟨0⟩\n\ndef count_at_most_two : State → Prop := fun s => s.count ≤ 2\n\ndef count_is_not_five : State → Prop := fun s => s.count ≠ 5\n\nend Cycle\n";

    #[test]
    fn the_induction_tests_each_invariant_then_all_together_and_reads_back() {
        let spec = parse(CYCLE).expect("it parses");
        let ids = [
            "Cycle.count_at_most_two.always",
            "Cycle.count_is_not_five.always",
        ];
        let induction = spec.induction(&ids);
        let group = |ids: &[&str]| ids.iter().map(ToString::to_string).collect::<Vec<_>>();
        assert_eq!(
            induction.groups,
            [group(&ids[..1]), group(&ids[1..]), group(&ids)]
        );
        assert!(
            induction
                .lean_code
                .starts_with("import Plausible\nimport Std.Data.HashSet\n")
        );
        assert!(induction.lean_code.contains(
            "(fun s => decide (Cycle.count_at_most_two s) && decide (Cycle.count_is_not_five s)) 1000))"
        ));
        let read = read_induction(
            &induction,
            &[
                "formal-inductive Cycle.count_at_most_two.always kept 120\n",
                "formal-inductive Cycle.count_is_not_five.always broken\u{1f}{ count := 4 }\u{1f}Cycle.Action.inc\u{1f}{ count := 5 }\n",
                "formal-inductive Cycle.count_at_most_two.always,Cycle.count_is_not_five.always kept 129\n",
            ],
        );
        assert_eq!(
            read,
            [
                (group(&ids[..1]), Inductive::Kept),
                (
                    group(&ids[1..]),
                    Inductive::Broken {
                        state: "{ count := 4 }".to_string(),
                        action: "Cycle.Action.inc".to_string(),
                        next: "{ count := 5 }".to_string(),
                    }
                ),
                (group(&ids), Inductive::Kept),
            ]
        );
        assert_eq!(
            read_induction(
                &induction,
                &["formal-inductive Cycle.count_at_most_two.always kept 0\n"]
            ),
            []
        );
        assert_ne!(spec.induction_key(&ids[..1]), spec.induction_key(&ids));
    }

    #[test]
    fn importing_formal_temporal_brings_formal_s_library_once_and_an_unknown_library_is_refused() {
        let dir = TempDir::new().expect("a temporary directory");
        write(
            &dir,
            "Base.lean",
            "import Formal.Temporal\n\nnamespace Base\n\ndef q : Prop := True\n\nend Base\n",
        );
        let path = write(
            &dir,
            "Live.lean",
            "import Formal.Temporal\nimport Spec.Base\n\nnamespace Live\n\ndef p : Prop := Temporal.always (0 : Nat) (fun n (_ : Unit) => n) (fun n => n = 0)\n\nend Live\n",
        );
        let spec = LeanSpec::load(&path).expect("it loads");
        assert_eq!(
            spec.source.matches("namespace Temporal").count(),
            1,
            "{}",
            spec.source
        );
        assert!(
            spec.source.contains("theorem leadsTo_of_measure"),
            "{}",
            spec.source
        );
        assert!(!spec.source.contains("import Formal"), "{}", spec.source);
        assert!(spec.source.find("namespace Temporal") < spec.source.find("namespace Base"));
        assert!(spec.source.find("namespace Base") < spec.source.find("namespace Live"));
        let unknown = write(
            &dir,
            "Unknown.lean",
            "import Formal.Missing\n\nnamespace Unknown\n\ndef p : Prop := True\n\nend Unknown\n",
        );
        assert_eq!(
            LeanSpec::load(&unknown)
                .map(|spec| spec.source)
                .map_err(|error| error.to_string()),
            Err(format!(
                "{unknown} imports `Formal.Missing`, which formal does not ship. formal ships `Formal.Temporal`"
            ))
        );
    }

    #[test]
    fn a_proof_that_repeats_the_imports_formal_resolves_leaves_them_to_formal() {
        let spec = parse(CYCLE).expect("it parses");
        let composed = spec.compose(
            "Cycle.count_at_most_two.always",
            "import Formal.Temporal\nimport Spec.Base\nimport Std.Data.HashSet\n\ntheorem t : True := trivial\n",
        );
        assert!(
            !composed.lean_code.contains("import Formal"),
            "{}",
            composed.lean_code
        );
        assert!(
            !composed.lean_code.contains("import Spec"),
            "{}",
            composed.lean_code
        );
        assert!(
            composed.lean_code.starts_with("import Std.Data.HashSet\n"),
            "{}",
            composed.lean_code
        );
    }

    const LIVE: &str = include_str!("../../../tests/fixtures/lean_spec/Live.lean");

    #[test]
    fn a_liveness_property_under_fairness_alone_is_checked_and_any_other_is_left_to_its_proof() {
        let spec = parse(LIVE).expect("it parses");
        let liveness = spec
            .machine
            .expect("a liveness property makes a machine")
            .liveness;
        let found: Vec<(&str, Vec<&str>, Option<&Predicate>, &Predicate)> = liveness
            .iter()
            .map(|live| {
                (
                    live.name.as_str(),
                    live.fair.iter().map(String::as_str).collect(),
                    live.start.as_ref(),
                    &live.goal,
                )
            })
            .collect();
        assert_eq!(
            found,
            [
                (
                    "a_fair_reset_empties_it",
                    vec!["Action.reset"],
                    Some(&Predicate::Named("positive".to_string())),
                    &Predicate::Term("(fun s => s.count = 0)".to_string())
                ),
                (
                    "two_comes",
                    vec!["Action.inc", "Action.reset"],
                    None,
                    &Predicate::Term("(fun s => s.count = 2)".to_string())
                ),
                (
                    "unfair",
                    vec![],
                    Some(&Predicate::Term("(fun s => 0 < s.count)".to_string())),
                    &Predicate::Term("(fun s => s.count = 0)".to_string())
                ),
            ]
        );
    }

    #[test]
    fn a_liveness_property_is_explored_on_the_machine_s_graph_and_its_lasso_read_back() {
        let spec = parse(LIVE).expect("it parses");
        assert_eq!(
            spec.explorable(),
            [
                "Live.positive.always",
                "Live.a_fair_reset_empties_it",
                "Live.two_comes",
                "Live.unfair"
            ]
        );
        let ids = [
            "Live.a_fair_reset_empties_it",
            "Live.two_comes",
            "Live.unfair",
        ];
        let exploration = spec.exploration(&ids);
        assert_eq!(exploration.ids, ids);
        assert!(exploration.lean_code.contains(
            "instance : DecidablePred Live.positive := fun s => by unfold Live.positive; infer_instance\nnamespace Live\n#eval IO.println (FormalLasso.report \"formal-bounded\" \"Live.a_fair_reset_empties_it\" (FormalLasso.search Live.init Live.step (FormalBounded.complete [Live.Action.inc, Live.Action.reset] (by intro a; cases a <;> simp)) [Action.reset] (some (fun s => decide (Live.positive s))) (fun s => decide ((fun s => s.count = 0) s)) 10 100000))\nend Live"
        ), "{}", exploration.lean_code);
        assert!(exploration.lean_code.contains(
            "[Action.inc, Action.reset] none (fun s => decide ((fun s => s.count = 2) s))"
        ));
        assert_ne!(spec.exploration_key(ids[0]), spec.exploration_key(ids[1]));
        let read = read_exploration(
            &exploration,
            &[
                "formal-bounded Live.a_fair_reset_empties_it bounded 10 3\n",
                "formal-bounded Live.two_comes lasso\u{1f}[]\u{1f}[Live.Action.inc, Live.Action.reset]\n",
                "formal-bounded Live.unfair lasso\u{1f}[Live.Action.inc, Live.Action.inc]\u{1f}[Live.Action.inc]\n",
            ],
        );
        assert_eq!(
            read,
            [
                (
                    ids[0].to_string(),
                    Explored::Bounded {
                        depth: 10,
                        states: 3
                    }
                ),
                (
                    ids[1].to_string(),
                    Explored::Lasso {
                        prefix: "[]".to_string(),
                        cycle: "[Live.Action.inc, Live.Action.reset]".to_string(),
                    }
                ),
                (
                    ids[2].to_string(),
                    Explored::Lasso {
                        prefix: "[Live.Action.inc, Live.Action.inc]".to_string(),
                        cycle: "[Live.Action.inc]".to_string(),
                    }
                ),
            ]
        );
    }

    #[test]
    fn a_machine_with_liveness_alone_leaves_run_to_the_spec() {
        let live = liveness_alone().replace(
            "end Live",
            "def run (actions : List Action) : State := actions.foldl step init\n\nend Live",
        );
        let spec = parse(&live).expect("a spec with no invariant may define run");
        let machine = spec
            .machine
            .as_ref()
            .expect("its liveness properties make a machine");
        assert_eq!(machine.invariants, Vec::<String>::new());
        assert_eq!(machine.liveness.len(), 3);
        assert!(!spec.source.contains("_root_.Live.run"), "{}", spec.source);
    }

    fn liveness_alone() -> String {
        LIVE.replace(
            "def positive : State → Prop := fun s => 0 < s.count\n\n",
            "",
        )
        .replace("positive (", "(fun s => 0 < s.count) (")
    }

    #[test]
    fn a_machine_with_liveness_alone_compares_its_own_run_and_derives_nothing_for_the_search() {
        let spec = parse(&liveness_alone().replace(
            "end Live",
            "/-- Runs.\n\n  code: src/live.rs run\n-/\ndef run (actions : List Action) : State := actions.foldl step init\n\ndef run.inputs : List (List Action) := [[], [.inc]]\n\nend Live",
        ))
        .expect("a spec with no invariant may compare its own run");
        let evaluation = spec.evaluation(&["Live.run"]);
        assert!(!evaluation.contains("FormalBounded.traces"), "{evaluation}");
        let search = spec.search(&["Live.two_comes"]).lean_code;
        assert!(!search.contains("deriving instance"), "{search}");
    }

    #[test]
    fn a_liveness_property_whose_body_holds_a_blank_or_comment_line_is_read_whole() {
        let spec = parse(&liveness_alone().replace(
            "def unfair : Prop :=",
            "def or_small : Prop :=\n  Temporal.eventually init step (fun _ => True) (fun s => s.count = 2)\n\n  -- or it stays small\n  ∨ Temporal.always init step (fun s => s.count ≤ 2)\n\ndef unfair : Prop :=",
        ))
        .expect("it parses");
        let names: Vec<String> = spec
            .machine
            .expect("its liveness properties make a machine")
            .liveness
            .into_iter()
            .map(|live| live.name)
            .collect();
        assert_eq!(names, ["a_fair_reset_empties_it", "two_comes", "unfair"]);
    }

    #[test]
    fn a_liveness_property_in_an_indented_namespace_ends_at_the_next_declaration() {
        let spec = parse(
            "namespace Live\n\n  inductive Action where\n    | inc\n\n  def init : Nat := 0\n\n  def step (n : Nat) : Action → Nat\n    | .inc => n + 1\n\n  def one_comes : Prop :=\n    Temporal.eventually init step (Temporal.fair Action.inc) (fun n => n = 1)\n  def two_comes : Prop :=\n    Temporal.eventually init step\n      (Temporal.fair Action.inc) (fun n => n = 2)\n  theorem unrelated : True := trivial\n\nend Live\n",
        )
        .expect("it parses");
        let names: Vec<String> = spec
            .machine
            .expect("its liveness properties make a machine")
            .liveness
            .into_iter()
            .map(|live| live.name)
            .collect();
        assert_eq!(names, ["one_comes", "two_comes"]);
    }

    #[test]
    fn a_machine_that_defines_run_is_refused() {
        let refused = parse(&COUNTER.replace(
            "end Counter",
            "def run (actions : List Action) : State := actions.foldl step init\n\nend Counter",
        ));
        assert!(
            matches!(refused, Err(SpecError::MachineRun(_))),
            "{refused:?}"
        );
    }

    #[test]
    fn the_search_derives_the_machine_types_and_unfolds_each_invariant() {
        let spec = parse(COUNTER).expect("it parses");
        let search = spec.search(&["Counter.count_below_three.always"]);
        for line in [
            "deriving instance Plausible.Arbitrary for Counter.Action",
            "deriving instance Plausible.Shrinkable for Counter.State",
            "deriving instance Repr for Counter.Action",
            "open FormalRefute in example : _root_.Counter.count_below_three.always := by unfold _root_.Counter.count_below_three.always _root_.Counter.count_below_three; plausible",
        ] {
            assert!(search.lean_code.contains(line), "{line}");
        }
    }

    #[test]
    fn the_search_key_is_its_own() {
        let spec = demo();
        assert_ne!(
            spec.search_key("Demo.double_even"),
            spec.key("Demo.double_even")
        );
        assert_ne!(
            spec.search_key("Demo.double_even"),
            spec.search_key("Demo.double_mono")
        );
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

    const TEXT: &str = "import Mathlib\n\nnamespace Text\n\ndef blank (s : List Char) : Bool := s.all (· = ' ')\n\nend Text\n";

    const USES: &str = "import Spec.Text\n\nnamespace Uses\n\ndef blank_is_all_space : Prop := ∀ s, Text.blank s = true → ∀ c ∈ s, c = ' '\n\nend Uses\n";

    fn write(dir: &TempDir, name: &str, text: &str) -> String {
        let path = dir.path().join(name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("a directory");
        }
        fs::write(&path, text).expect("written");
        path.to_string_lossy().to_string()
    }

    #[test]
    fn an_imported_spec_comes_before_the_spec_and_its_imports_go_to_the_top() {
        let dir = TempDir::new().expect("a temporary directory");
        write(&dir, "Text.lean", TEXT);
        let spec = LeanSpec::load(&write(&dir, "Uses.lean", USES)).expect("it loads");
        assert_eq!(spec.properties, ["Uses.blank_is_all_space"]);
        assert!(
            spec.source.starts_with("import Mathlib\n"),
            "{}",
            spec.source
        );
        assert!(!spec.source.contains("Spec.Text"), "{}", spec.source);
        let text = spec
            .source
            .find("namespace Text")
            .expect("the import is in");
        let uses = spec.source.find("namespace Uses").expect("the spec is in");
        assert!(text < uses, "{}", spec.source);
        let composed = spec.compose("Uses.blank_is_all_space", "theorem t : True := trivial");
        assert!(
            composed.lean_code.starts_with("import Mathlib\n"),
            "{}",
            composed.lean_code
        );
        assert!(
            composed.lean_code.contains("namespace Text"),
            "{}",
            composed.lean_code
        );
    }

    #[test]
    fn a_spec_without_a_spec_import_reads_as_its_own_text() {
        let dir = TempDir::new().expect("a temporary directory");
        let text = TEXT.replace("end Text", "def p : Prop := True\n\nend Text");
        let spec = LeanSpec::load(&write(&dir, "Text.lean", &text)).expect("it loads");
        assert_eq!(spec.source, text);
    }

    #[test]
    fn an_edit_to_an_imported_spec_moves_the_keys_of_the_spec() {
        let dir = TempDir::new().expect("a temporary directory");
        write(&dir, "Text.lean", TEXT);
        let path = write(&dir, "Uses.lean", USES);
        let before = LeanSpec::load(&path)
            .expect("it loads")
            .key("Uses.blank_is_all_space");
        write(&dir, "Text.lean", &TEXT.replace("(· = ' ')", "(· == ' ')"));
        let after = LeanSpec::load(&path)
            .expect("it loads")
            .key("Uses.blank_is_all_space");
        assert_ne!(before, after);
    }

    #[test]
    fn a_spec_imported_twice_comes_in_once_and_a_nested_name_is_a_directory() {
        let dir = TempDir::new().expect("a temporary directory");
        write(&dir, "Lib/Text.lean", TEXT);
        write(
            &dir,
            "Words.lean",
            "import Spec.Lib.Text\n\nnamespace Words\n\ndef none : List Char := []\n\nend Words\n",
        );
        let path = write(
            &dir,
            "Uses.lean",
            &USES.replace(
                "import Spec.Text",
                "import Spec.Lib.Text\nimport Spec.Words",
            ),
        );
        let spec = LeanSpec::load(&path).expect("it loads");
        assert_eq!(
            spec.source.matches("namespace Text").count(),
            1,
            "{}",
            spec.source
        );
        assert!(spec.source.find("namespace Text") < spec.source.find("namespace Words"));
    }

    #[test]
    fn every_import_resolves_from_the_directory_of_the_spec_the_session_opens_on() {
        let dir = TempDir::new().expect("a temporary directory");
        write(&dir, "Text.lean", TEXT);
        write(
            &dir,
            "Lib/Inner.lean",
            "import Spec.Text\n\nnamespace Inner\n\nend Inner\n",
        );
        let top = write(
            &dir,
            "Top.lean",
            &USES.replace("import Spec.Text", "import Spec.Lib.Inner"),
        );
        assert!(LeanSpec::load(&top).is_ok(), "{:?}", LeanSpec::load(&top));
        let inner = write(
            &dir,
            "Lib/Inner.lean",
            "import Spec.Text\n\nnamespace Inner\n\ndef p : Prop := True\n\nend Inner\n",
        );
        assert!(
            matches!(LeanSpec::load(&inner), Err(SpecError::NoSuchImport { ref path, .. }) if path.ends_with("Lib/Text.lean")),
            "{:?}",
            LeanSpec::load(&inner)
        );
    }

    #[test]
    fn a_missing_import_a_cycle_and_an_import_that_runs_code_are_refused() {
        let dir = TempDir::new().expect("a temporary directory");
        let path = write(&dir, "Uses.lean", USES);
        assert!(
            matches!(LeanSpec::load(&path), Err(SpecError::NoSuchImport { ref import, .. }) if import == "Spec.Text"),
            "{:?}",
            LeanSpec::load(&path)
        );
        write(
            &dir,
            "Text.lean",
            &format!("import Spec.Uses\n{TEXT}").replace(
                "import Spec.Uses\nimport Mathlib",
                "import Mathlib\nimport Spec.Uses",
            ),
        );
        assert!(
            matches!(LeanSpec::load(&path), Err(SpecError::ImportCycle { .. })),
            "{:?}",
            LeanSpec::load(&path)
        );
        write(&dir, "Text.lean", &format!("{TEXT}\n#eval 1\n"));
        assert!(
            matches!(LeanSpec::load(&path), Err(SpecError::RunsCode { ref found, .. }) if found == "#eval"),
            "{:?}",
            LeanSpec::load(&path)
        );
    }
}
