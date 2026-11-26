# formal

[![Checks](https://github.com/yamafaktory/formal/actions/workflows/checks.yml/badge.svg)](https://github.com/yamafaktory/formal/actions/workflows/checks.yml)

**Property checker for code, backed by Lean 4 and Mathlib. Your agent writes the
properties and the proofs; formal checks them.**

Take a function that applies a discount. The property to establish: for every
non-negative price and every rate, the result lies between 0 and the price. Your agent
states it as a Lean theorem and writes a proof. formal has Lean check the proof and
returns the verdict: verified, or rejected with Lean's first error and a hint.

formal does not call a model. It needs no API key and has no opinion about which model
you use. The agent that already reads your code writes the Lean. formal does everything
that needs no model:

- it checks proofs, in Lean processes that keep Mathlib loaded between checks,
- it retries a rejected proof with an automatic tactic chain, then a Mathlib premise
  search (`exact?`),
- it audits the axioms every accepted proof depends on,
- it caches every proof that passes, and
- it detects when the code changes under a property.

## How it works

Three judgements precede any Lean run, and your agent makes all three:

1. **Decomposition.** Which parts of the code are pure functions. Code with side effects,
   such as database calls, HTTP or file access, is out of scope.
2. **Property extraction.** What those functions must satisfy, with explicit
   preconditions and modelling assumptions.
3. **Formalization.** The Lean 4 theorem that states the property.

Then Lean checks the proof. Its kernel is sound: a proof it accepts is a valid derivation
of the stated theorem. But Lean checks only the theorem it receives. If the formalization
misreads the function, Lean proves a true theorem about a different function. Read
[What a result means](#what-a-result-means) before you rely on a result.

## Quick start

On Linux and macOS (x86_64 or arm64), install the prebuilt binary:

```sh
curl -fsSL https://github.com/yamafaktory/formal/releases/latest/download/install.sh | sh
formal setup
formal status
```

The script checks the SHA-256 of the download and puts `formal` in `~/.local/bin`.
Set `FORMAL_INSTALL_DIR` to install somewhere else, and `FORMAL_VERSION=v1.0.0` to pin a
release. The Linux binary is static, so it runs on any distribution.

On another platform, or to build from source, you need a Rust toolchain:

```sh
cargo install --git https://github.com/yamafaktory/formal formal-cli
```

`formal setup` installs [elan](https://github.com/leanprover/elan) and the pinned Lean
version. Then it downloads Mathlib's prebuilt oleans (compiled Lean modules, several GB
the first time), and builds the [Lean REPL](https://github.com/leanprover-community/repl)
that keeps Mathlib loaded. It asks before the large download. You can run it again
safely: it skips every step that is already done.

The binary carries its own Lean project and creates it under `~/.local/share/formal`. You
do not need to clone this repository. A binary built from a clone keeps its Lean project
and results inside the clone instead.

formal uses any elan already on your system, and changes nothing in your shell
configuration.

Start the server:

```sh
formal serve --background   # returns once the server answers, or at once if it already runs
formal status               # … server  http://127.0.0.1:1337 (running)
formal stop
```

## A worked example

This is a real session. The responses below come from formal itself.

**The function.** `ring.py`:

```python
def wrap(index, size):
    return index % size
```

**The spec.** The agent models the function in Lean and states the property it wants.
The `code:` line names the code the model describes, and `wrap.inputs` lists the inputs
to compare the two on. Lean's `%` on `Int` looks like the obvious model:

```lean
namespace Ring

/-- code: ring.py wrap -/
def wrap (input : Int × Int) : Int := input.1 % input.2

def wrap.inputs : List (Int × Int) :=
  [(7, 3), (-7, 3), (0, 3), (7, -3), (-7, -3)]

def in_range : Prop :=
  ∀ index size : Int, 0 < size → 0 ≤ wrap (index, size) ∧ wrap (index, size) < size

end Ring
```

**The session.** The agent opens a session on the spec:

```sh
curl -s -X POST localhost:1337/session -H 'content-type: application/json' \
  -d '{"spec": "/abs/path/to/Ring.lean"}'
```

```json
{
  "session_id": "c4a8585c…", "cached": [], "work": ["Ring.in_range"], "complete": false, "stale": [],
  "compare": [{
    "function": "Ring.wrap", "code": "ring.py wrap",
    "inputs": [[7, 3], [-7, 3], [0, 3], [7, -3], [-7, -3]]
  }],
  "refuted": [], "bounded": [], "not_inductive": [], "inductive_together": []
}
```

**The comparison.** The agent runs `wrap` from `ring.py` on each input and sends the
answers:

```sh
curl -s -X POST localhost:1337/session/$SID/compare -H 'content-type: application/json' \
  -d '{"answers": {"Ring.wrap": [1, 2, 0, -2, -1]}}'
```

```json
{ "matched": [], "differed": [{ "function": "Ring.wrap", "input": [7, -3], "spec": 1, "code": -2 }] }
```

The model is wrong. Python's `%` takes the sign of the divisor, and Lean's `%` on `Int`
is non-negative whenever the divisor is not zero. A proof about this model would hold, and say nothing about `ring.py`.
The agent changes the model to `Int.fmod`, Lean's floor modulo, which matches Python:

```lean
def wrap (input : Int × Int) : Int := Int.fmod input.1 input.2
```

It opens the session again and sends the same answers:

```json
{ "matched": ["Ring.wrap"], "differed": [] }
```

**A first proof.** The proof leaves the spec out. formal puts the spec before it:

```lean
theorem Ring.in_range.holds : Ring.in_range := by
  intro index size h
  unfold Ring.wrap
  omega
```

```sh
curl -s -X POST localhost:1337/session/$SID/check -H 'content-type: application/json' \
  -d '{"proof_files": {"Ring.in_range": "/abs/path/to/proofs/in_range.lean"}}'
```

```json
{
  "verified": [],
  "recovered": [],
  "failed": [{
    "id": "Ring.in_range",
    "error": "omega could not prove the goal:\na possible counterexample may satisfy the constraints\n  b ≤ -1\n  a ≥ 1\nwhere\n a := size\n b := (index, size).fst.fmod (index, size).snd",
    "line": 4, "col": 2,
    "hint": "`omega` reasons about linear integer arithmetic only — every other subterm is an opaque variable to it, which is why the counterexample it prints mentions terms you expected to have been reduced away.\nLook at the `where` block in the error: if the same value appears under two different names (typically an unreduced projection such as `(a, b).2` alongside the `b` it should have become), omega cannot know they are equal. Reduce it before calling omega — `simp` the projection away, rewrite with the lemma that states the equality, or prove the arithmetic fact as a standalone `have` over the already-reduced form and close the goal with `simpa using` it.\nAdding more hypotheses to omega will not help while the terms remain opaque."
  }],
  "remaining": ["Ring.in_range"],
  "complete": false
}
```

formal first tried to recover the proof on its own, and failed. The error shows why:
`omega` treats `fmod` as an unknown value `b`, so it cannot rule out `b ≤ -1`. The hint
says so, and names three ways out. The fix takes the last one: it proves each bound as a
`have`, then closes the goal with them.

**The fix.** The agent states both bounds with the lemmas core Lean has for `Int.fmod`:

```lean
theorem Ring.in_range.holds : Ring.in_range := by
  intro index size h
  have lo := Int.fmod_nonneg_of_pos index h
  have hi := Int.fmod_lt_of_pos index h
  exact ⟨lo, hi⟩
```

```json
{ "verified": ["Ring.in_range"], "recovered": [], "failed": [], "remaining": [], "complete": true }
```

This check took 0.67 s. The spec and the proof use core Lean only, so Lean loaded no Mathlib.

**Next time.** formal stores the accepted proof. A later session on the same spec finds
it:

```json
{
  "session_id": "9a1a53e4…",
  "cached": [{ "id": "Ring.in_range", "description": "", "kind": "spec", "assumptions": [] }],
  "work": [], "complete": true, "stale": [],
  "compare": [{
    "function": "Ring.wrap", "code": "ring.py wrap",
    "inputs": [[7, 3], [-7, 3], [0, 3], [7, -3], [-7, -3]]
  }],
  "refuted": [], "bounded": [], "not_inductive": [], "inductive_together": []
}
```

The comparison and the proof check different things. The comparison holds the model to
the code, on the inputs it lists. The proof holds the property to the model, for every
input.

## Using formal from an agent

### Tell your agent about it

For Claude Code, add this to `CLAUDE.md`. For other agents, use their equivalent file.

````markdown
## Formal verification

After writing or changing non-trivial pure logic — calculations, transformations,
validations, business rules — verify it with formal:

1. `formal serve --background` (safe to run every time; no-op if already up)
2. `curl -s localhost:1337/guide` and follow the workflow it returns

Skip it for I/O, controller wiring, configuration and tests.

Properties live in `formal.properties.json` and are committed. Read the preconditions
and assumptions before trusting a result: if they do not match what you intended, the
proof is not evidence about your code. A `stale` id means the function changed and its
property needs rewriting.
````

### The loop

formal serves its instructions in stages. An agent reads the Lean conventions only once it
starts to write Lean.

```
GET  /guide                      the workflow and the spec file schema
GET  /guide/extract              how to find pure functions and their properties
     → write formal.properties.json, commit it
POST /session {"spec_file": …}   → {cached, work, stale}
GET  /guide/formalize            how to state a property in Lean, and how to check the statement
GET  /guide/tactics              the proof failures that come up most, and how to avoid them
GET  /guide/machines             how to specify a state machine, its invariants and its liveness
POST /session/{id}/check         {"proofs": {"<id>": "<lean>"}} or {"proof_files": {"<id>": "<path>"}}
     → {verified, recovered, failed, remaining, complete}
     fix the failures, send only those ids again, repeat
POST /session/{id}/compare       {"answers": {"<function>": [...]}}
     → {matched, differed}
```

Three things keep the loop cheap:

- **Properties are registered once.** A retry sends only the corrected Lean.
- **A failure comes back short.** formal returns the first error and a hint, never Lean's
  full output, which for a Mathlib failure runs to thousands of tokens.
- **formal recovers what it can.** Before it reports a failure, it replaces the proof
  with an automatic tactic chain, then with a premise search (`exact?`). On a spec
  property, the chain first unfolds the property and the spec's definitions, and
  introduces the variables. It tries `rfl`, `omega`, `decide`, `simp`, `simp_all` and
  `grind`. When the file imports Mathlib, it also tries `norm_num`, `linarith`, `ring`,
  `positivity` and `nlinarith`. A proof recovered this way appears under `recovered`
  and never goes back to the agent.

### One command: `formal check`

`formal check <spec>` runs the whole loop on a Lean spec in one process, with no server.
It runs the counterexample search, checks each proof it finds at
`proofs/<Namespace>/<name>.lean`, compares the code's answers when you pass them, and
exits. For a property with no proof file, it tries the tactic chain first. A property
the chain proves prints `verified by formal's own tactics`, and the agent writes no proof
for it. It prints one line per property and per compared function, and no log lines. The
exit code is:

- 0 when everything holds.
- 1 when something does not.
- 2 when formal cannot run the check: it cannot read the spec or the answers, the answers
  name a function the spec does not compare or have the wrong count, or formal cannot run
  Lean.

On the spec of the [worked example](#a-worked-example), before any proof or answer:

```
$ formal check Ring.lean
· Ring.in_range  no proof: write proofs/Ring/in_range.lean declaring `theorem Ring.in_range.holds : Ring.in_range`
· Ring.wrap  compare: run ring.py wrap on [[7,3],[-7,3],[0,3],[7,-3],[-7,-3]], then pass --answers <file> holding {"Ring.wrap": [answers]}
0 of 1 properties hold, 0 of 1 functions match the code
```

Once the proof and the answers are in place:

```
$ formal check Ring.lean --answers answers.json
✓ Ring.in_range  verified
✓ Ring.wrap  matches ring.py wrap
1 of 1 properties hold, 1 of 1 functions match the code
```

- `--proofs <dir>` reads the proofs from another directory. The default, `proofs`, is
  relative to the current directory, not to the spec.
- `--inputs <file>` writes the inputs of each compared function to that file, as
  `{"<function>": [inputs]}`. A function with many inputs prints only their count.
- A hint that already appeared in the run appears again as `hint: as above`.

### The spec file

Properties live in a JSON file that you commit next to the code. For example, this file
holds one entry:

```json
{
  "version": 1,
  "properties": [
    {
      "id": "apply_discount/bounded",
      "function": "apply_discount",
      "kind": "invariant",
      "formal": "forall price rate, 0 <= price -> 0 <= apply_discount price rate /\\ apply_discount price rate <= price",
      "description": "a discounted price is never negative and never above the original price",
      "preconditions": ["price is not negative"],
      "assumptions": ["prices and rates modelled as rationals, not floats"],
      "source_file": "pricing.py",
      "function_code": "def apply_discount(price, rate):\n    rate = max(0.0, min(rate, 1.0))\n    return price * (1 - rate)\n"
    }
  ]
}
```

`id`, `function`, `kind` and
`formal` are required. formal resolves `source_file` against the spec file's directory,
or against `root` when you pass one. Send `spec_file` as an absolute path: the server
resolves it, and its working directory is not yours.

**Commit the file.** The cache depends on it. Two independent runs over one small function
produced six and seven properties. They agreed on the wording of none of them, and stated
one of them in opposite directions. A cache cannot match properties that change on every
run. A committed file is the same every time, so a proof is written once and reused.

A committed file is also reviewable. It shows what was checked last week, and a diff
shows when the answer changes.

### A Lean spec

A spec file asks each proof to bring its own Lean model of the code, and two proofs can
model the same function differently. A Lean spec holds one model for all of them. It
defines the model inside one namespace, and states each property as `def <name> : Prop`.
This excerpt is shortened from `spec/Pystr.lean`:

```lean
namespace Pystr

def rstrip (s : List Char) : List Char := (s.reverse.dropWhile isSpace).reverse

def rstrip_idempotent : Prop :=
  ∀ s, rstrip (rstrip s) = rstrip s

end Pystr
```

Open a session with `{"spec": "/abs/path/to/Pystr.lean"}`. Each property comes back as
work under `<Namespace>.<name>`, here `Pystr.rstrip_idempotent`. Its proof leaves the
spec out and declares `theorem Pystr.rstrip_idempotent.holds : Pystr.rstrip_idempotent`.
formal puts the spec before the proof and holds the proof to the spec's own statement.
A proof that redefines a name of the spec fails. The cache key covers the whole spec, so
an edit to the spec sends every property back as work.

A spec can reuse another spec's definitions. `import Spec.Pystr` in its header makes formal
read `Pystr.lean` from the directory of the spec the session opens on, and put it before the
spec. Nested imports resolve from that same directory, as Lean resolves modules from one
root. A dotted name, such as `Spec.Lib.Text`, reads from a subdirectory. Properties come only from the spec the
session opens on. The cache key covers every imported spec too, and formal refuses an
import it cannot find, a cycle, and an imported spec that can run code.

A Lean spec can also hold the code to its model. A function names the code it describes
in a `code:` line of its doc comment, and `def <name>.inputs` lists the inputs:

```lean
/-- code: rust/formal-core/src/pystr.rs rstrip -/
def rstrip (s : List Char) : List Char := (s.reverse.dropWhile isSpace).reverse

def rstrip.inputs : List (List Char) := words 4
```

formal evaluates the inputs in Lean when the session opens. The session lists each such
function under `compare`, with its inputs as JSON. Inputs and answers cross through
Lean's `ToJson`, and a `List Char` crosses as a JSON string. Core Lean has instances for
`Nat`, `Int`, `Bool`, `String`, lists, pairs and options. A spec cannot name `Lean`, so it
cannot add an instance for a type of its own.
The caller runs its own code on each input and sends the answers to
`POST /session/{id}/compare`. formal keeps the spec's answers to itself. It answers with
the functions that `matched`. Each function that `differed` comes with the first input
where the two disagree, the spec's answer and the code's answer.

A spec can describe a state machine. It defines `init : State`,
`step : State → Action → State` and at least one invariant in its namespace. An invariant
is a `def <name> : State → Prop`, or a `def <name> (s : State) : Prop`. formal defines
`run`, the fold of `step` over a list of actions from `init`, and registers each invariant
as `<Namespace>.<name>.always`, which says that it holds in every reachable state:

```lean
def count_at_most_two : State → Prop := fun s => s.count ≤ 2
```

In a spec with the namespace `Bounded`, formal registers `Bounded.count_at_most_two.always`,
which states `∀ actions, count_at_most_two (run actions)`. Its proof declares
`theorem Bounded.count_at_most_two.always.holds : Bounded.count_at_most_two.always`. The
search derives generators for the spec's types, so a broken invariant comes back with the
list of actions that breaks it.

When the actions are known, formal also explores every reachable state up to a depth,
10 unless the spec defines `def depth : Nat`. The actions are the constructors of the
action type when none takes an argument, else `<Action>.samples`. formal visits each
state once, so a violation comes back under `refuted` with a shortest trace. An invariant
that held comes back under `bounded`, with the depth and the number of states:

```json
"bounded": [{"id": "Bounded.count_at_most_two.always", "depth": 10, "states": 3}]
```

The check stops after 100,000 states, and `bounded` then gives the last depth it explored
in full. Lean proves the list of constructors complete before the check uses it, so a
missed action can only skip the check, never claim a bound. An invariant Lean cannot
decide is left out of the check. Only a proof settles it.

A `code:` line on `step` holds the code to the machine. The session lists `Bounded.run`
under `compare`, with one trace of actions per state the bounded walk reached. The caller
replays each trace on its code and sends the last state to `POST /session/{id}/compare`,
and formal names the first trace where the code's state differs from the spec's. Actions
and states cross in Lean's derived JSON:

```json
{
  "inputs": [[], ["inc"], ["inc", "inc"]],
  "answers": {"Bounded.run": [{"count": 0}, {"count": 1}, {"count": 2}]}
}
```

A structure crosses as an object of its fields, and text as a string. A constructor with
no argument crosses as its name, one with named arguments as `{"add": {"n": 1}}`, one with
one anonymous argument as `{"one": 1}`, and one with several as `{"two": [2, false]}`.
`Option.none` crosses as `null`. A trace of `Char` actions crosses as a string.

formal also tests whether each invariant the checks did not refute is inductive, the
shape a proof by induction needs. It draws states where the invariant holds, takes every
action, and checks the next state. A state where a step breaks it comes back under
`not_inductive`, with the action and the next state, so its proof needs a stronger
invariant. When several such invariants are kept by every step together,
`inductive_together` names them, and one induction proves them all:

```json
"not_inductive": [{"id": "Cycle.count_is_not_five.always", "state": "{ count := 4 }", "action": "Cycle.Action.inc", "next": "{ count := 5 }"}],
"inductive_together": ["Cycle.count_at_most_two.always", "Cycle.count_is_not_five.always"]
```

`<State>.samples` steers the drawn states, as `<Type>.samples` steers the search.

Liveness says that something good eventually happens. `import Formal.Temporal` gives a
spec formal's temporal library. It defines the operators over a machine's `init` and `step`:

- `Temporal.always init step p`: `p` holds in every state the machine reaches.
- `Temporal.eventually init step assumed p`: every run that satisfies `assumed` reaches a
  state where `p` holds.
- `Temporal.leadsTo init step assumed p q`: in every run that satisfies `assumed`, each
  state where `p` holds is followed by a state where `q` holds, or is one.
- `Temporal.fair a`: the run takes the action `a` again and again. That is weak fairness,
  since every action can always be taken.

Fairness holds only where a property states it:

```lean
import Formal.Temporal

def a_fair_reset_empties_the_count : Prop :=
  Temporal.leadsTo init step (Temporal.fair Action.reset) (fun s => 0 < s.count) (fun s => s.count = 0)
```

`eventually` and `leadsTo` also claim that some run satisfies `assumed`. An assumption no
run meets therefore makes the property false, not true for want of a run. For one fair
action, `⟨_, Temporal.fair_constant a⟩` gives that run. For several, `Temporal.cycle`
repeats a list of actions, and `Temporal.fair_cycle` proves each listed action fair in it:

```lean
⟨_, Temporal.fair_cycle Action.drain [Action.wait] Action.drain (by simp),
  Temporal.fair_cycle Action.drain [Action.wait] Action.wait (by simp)⟩
```

The library proves its own rules:

- `Temporal.always_of_inductive` proves `always` from an inductive invariant.
- `Temporal.leadsTo_of_measure` proves `leadsTo` from a fair action and a measure. Every
  step from `p` reaches `q`, or keeps `p` and does not raise the measure. The fair action
  reaches `q`, or keeps `p` and lowers the measure. An invariant proved with `always`
  limits both to the states where it holds. `Temporal.always_true` stands in when there is
  none.
- `Temporal.leadsTo_of_fair_step` is that rule without a measure: the fair action reaches
  `q` at once.
- `Temporal.leadsTo_trans` chains two `leadsTo`. `Temporal.leadsTo_or` joins two that
  reach the same `q`, and `Temporal.leadsTo_of_imp` gives `leadsTo p q` when `p` implies `q`.
- `Temporal.eventually_of_leadsTo` gives `eventually q` from `leadsTo p q` when `init`
  satisfies `p`.

The library is core Lean, in `rust/formal-core/lean/Temporal.lean`. To compile a spec
without formal, paste the file in place of the import. formal refuses any other `Formal.`
import, and leaves out a `Formal.` or `Spec.` import that a proof repeats.

When the session opens, formal also looks for a run that breaks each liveness property. It
checks a property written as `Temporal.leadsTo init step A p q` or
`Temporal.eventually init step A q`, where `A` is `Temporal.fair a`, several of them joined
with `∧`, or `fun _ => True`. On the states the bounded walk reaches, a violation is a loop
that takes every fair action and never reaches `q`. It comes back under `refuted`:

```json
{"id": "Live.a_reset_empties_the_count_without_fairness", "counterexample": ["actions := [Live.Action.inc, Live.Action.inc]", "then forever := [Live.Action.inc]"], "issue": "on this fair run, what the property promises never comes"}
```

A property that held comes back under `bounded` only when the walk reached every state its
actions lead to. A
walk cut at its depth gives no answer, since the loop may lie past it. A fair action that
`<Action>.samples` leaves out also gives no answer, since the walk never takes it. Any other
shape is left to its proof.

When the session opens, formal also searches each property for a counterexample with
Plausible. A false property comes back under `refuted`, with the value of each variable
and what does not hold. For this false property in a spec with the namespace `Demo`:

```lean
def double (n : Nat) : Nat := n + n

def double_odd : Prop := ∀ n, double n % 2 = 1
```

the session answers:

```json
"refuted": [{"id": "Demo.double_odd", "counterexample": ["n := 0"], "issue": "0 = 1 does not hold"}]
```

The property stays under `work`. Fix the spec, and open the session again. A property the
search cannot test refutes nothing, and its proof decides it. Random values rarely hit a
rare input, so a spec can list values for a type, as `def <Type>.samples : List <Type>`.
The search then draws half of the values of that type from that list. `spec/Pystr.lean`
lists its `alphabet` as `Char.samples`.

### Stale properties

A committed property can outlive its code. Each property records the function source it
was written against, in `function_code`. When that source changes, formal reports the
property as `stale` and does not check it:

```json
{ "work": [], "cached": [], "stale": ["apply_discount/bounded"], "complete": false }
```

A proof against code the property no longer describes yields a true theorem about
nothing, so formal declines to check it. Read the function again, update the property and
its `function_code`, and the session completes again.

formal compares normalised text, not a parse, so this works for any language. Trailing
whitespace is not a change. Indentation is: a function that moves one level deeper
becomes stale, and its `function_code` needs the new indentation. A property without a
`source_file` cannot become stale, because there is nothing to compare it with.

### formal's own properties

formal checks itself through Lean specs, one per module of its own code.

- `spec/Pystr.lean` specifies the Python string rules the cache key depends on.
- `spec/ProofCache.lean` imports it and specifies the cache key. Two of its properties
  guard against collisions that really happened: an operator spelled as a word counts only
  at a word boundary, and no field of the key can imitate the boundary between two others.
  Its word boundary follows Unicode, as the regex in Rust does: the spec holds the regex's
  table of word characters, and the compare checks it on every code point. The kind is
  lowercased as ASCII, in the spec and in Rust.
- `spec/Hints.lean` specifies how formal picks the advice for a failed proof: the first
  rule that claims the error and answers wins.
- `spec/Run.lean` specifies how formal reads Lean's verdict: a `sorry` is a warning to
  Lean and a failure here, and the first error Lean reported stays first.
- `spec/Specs.lean` imports `spec/ProofCache.lean` and specifies how formal reads a spec
  file: when a property is stale, when two ids clash, and which fields are missing.
- `spec/Verifier.lean` specifies how formal prepares a proof: imports split from the body,
  proofs batched into one file with each error traced back to its proof, the pre-check, and
  the rewrites that try an automatic tactic.

Their proofs are in `proofs/<Namespace>/`. The test `formal-service/tests/spec_sessions.rs`
checks every proof of every spec, and `formal-lean/tests/spec.rs` compares the code in
Rust with each spec that names its code in a `code:` line.

## What a result means

### What "verified" means

Lean's kernel accepted a proof of a theorem derived from your code, relative to Mathlib
and the axioms `propext`, `Classical.choice` and `Quot.sound`. That is strong evidence
against logical errors, which models make and Lean catches. It is not a proof that your
source code is correct: the theorem concerns a Lean model of the code, and nothing
certifies that the model is faithful.

formal is good for:

- catching logical errors in generated code that tests might miss,
- stating the assumptions about your code explicitly,
- confidence in pure logic: calculations, transformations, validations, and
- a machine-checked record of what holds, and under which assumptions.

formal does not give you:

- a guarantee that your source code is correct, only that a Lean model of it satisfies
  the stated properties,
- complete coverage, because whoever writes the properties chooses them and can miss
  important ones, or
- formal verification in the traditional sense, which requires a certified translation
  from source code to Lean. formal has none.

Properties that depend on reference equality, reflection or runtime behaviour lie outside
what a Lean model can express. They are classified `unverifiable`: a limit of the
modelling, not a failed proof.

### What formal refuses

A file that Lean accepts does not always establish its theorems. Lean accepts a theorem
derived from an axiom the file itself declares, and `axiom cheat : False` derives
anything. `#exit` ends elaboration without an error, so no declaration after it is
checked. formal closes both gaps:

- **It refuses proofs that can run code.** Code that runs during a check could print a
  fake verdict. formal refuses `#eval`, `#exit`, `#guard_msgs`, `run_cmd` and the other
  `run_` commands, `elab`, `macro`, `syntax`, `initialize`, `unsafe`, `implemented_by`,
  `extern`, and the `IO` and `Lean` namespaces. It ignores these words inside comments.
- **It audits the axiomatic dependencies of every declaration.** The audit is a Lean
  module, `FormalAudit`, that formal compiles on first use. Each check imports it, so
  Lean elaborates the audit before it reads the proof, and nothing the proof declares,
  a notation included, can change what the audit does. The audit lists every
  declaration that depends, directly or through other declarations in the file, on an
  axiom other than `propext`, `Classical.choice` and `Quot.sound`. That includes an
  `example`, which Lean checks and then discards. A declared axiom, a
  `sorry` (`sorryAx`) or `native_decide` fails the check at the line of that
  declaration. This also catches a `sorry` whose warning `#guard_msgs` suppresses.
- **It checks every declaration with the kernel again.** The audit adds a copy of each
  declaration in the file under a new name, and the kernel checks the copy. An option
  such as `debug.skipKernelTC` lets a declaration skip the kernel, but its copy cannot,
  so the check fails however the option is spelled.
- **It requires the audit to report.** The report carries a random nonce that the proof
  cannot know. If no report comes back, the check fails. This happens when elaboration
  stops before the end of the file, for example at an unclosed comment. A file that ends
  in `... in` fails before Lean runs, because the `in` would apply to the audit.

The audit takes imported Mathlib declarations as built, the same trust Lean extends to
them. formal compiles the audit once for each version of formal and of Lean, which takes about
a second.

### Check the statement yourself

Lean guarantees that the stated theorem follows from its axioms. It cannot tell you
whether that theorem is the property you meant. If the formalization misread your code,
Lean proves the wrong statement and reports success. This failure is indistinguishable
from a pass, which makes it the one formal is least able to detect.

`GET /guide/formalize` includes questions for the agent to put to its own theorem before
it submits:

- Is every hypothesis necessary, or does it narrow the claim only so that the proof goes
  through?
- Are the hypotheses jointly satisfiable, or is the theorem vacuous?
- Is it trivially true, a restatement of the definition that `rfl` closes?
- Are the quantifiers, and the direction of every implication and equivalence, those of
  the property?
- Does it still match the `formal` and `description` fields of the spec file?

This check is not blinded. The agent read both the property and its theorem, and cannot
unread either. formal once ran a blinded check: it translated each theorem back into
English without the original description, so it compared two independent readings. That
check left with the model pipeline, and the self check is a weaker replacement.

So read the result the way a reviewer would. On a cache hit, formal reports the
description and assumptions recorded with the proof. If that model is not yours, the hit
is not the property you meant.

### Limitations

- **The agent decides what is checked.** It can misread code, miss properties, or write
  theorems that are true but beside the point. formal has no second opinion to offer.
- **Preconditions and assumptions can be wrong.** A proof that rests on a wrong
  assumption is not evidence about your code.
- **Only pure logic.** formal excludes side effects by design.
- **Modelling limits.** Floats are modelled as rationals, and strings with structural
  equality. IEEE 754 rounding and reference semantics fall outside the model.
- **It does not replace tests.** formal establishes a property for all inputs that
  satisfy the stated assumptions. It does not replace integration or end-to-end tests.
- **Complex proofs can time out.** Raise `LEAN_TIMEOUT` if they do.
- **The first install is large.** Mathlib's prebuilt oleans take several GB and a few
  minutes, once, during `formal setup`.

## API reference

`formal serve` listens on `127.0.0.1:1337` (`FORMAL_HOST`, `FORMAL_PORT`).
`GET /openapi.json` gives the full schema of every request and response.

| Endpoint | Purpose |
|---|---|
| `GET /health` | Answers when the server is up |
| `GET /openapi.json` | The full schema |
| `GET /guide` | The workflow, the spec file schema and the topic list |
| `GET /guide/{extract\|formalize\|tactics\|machines}` | The instructions for one phase |
| `POST /session` | `{"spec_file": path, "root"?: path}`, `{"spec": path}`, or `{"properties": [...]}` |
| `GET /session/{id}` | The current state of a session |
| `POST /session/{id}/check` | `{"proofs": {id: lean}}`, or `{"proof_files": {id: path}}` |
| `GET /session/{id}/proof/{property_id}` | The proof Lean accepted for one property |
| `DELETE /session/{id}` | Close a session early |

A session expires after `SESSION_TTL_MINUTES` of inactivity (default 60). Inline
`properties` suit a one off check, but nothing carries over to a later run. Paths in
`proof_files` must be absolute, like `spec_file` and `spec`.

## Running formal

### Configuration

formal reads an optional `.env` file in `FORMAL_HOME`. Environment variables override
it. `formal status` prints the values in use and names any key in `.env` that nothing
reads.

| Variable | Meaning |
|---|---|
| `FORMAL_HOST` | Address the server listens on (default `127.0.0.1`) |
| `FORMAL_PORT` | Port the server listens on (default `1337`) |
| `SESSION_TTL_MINUTES` | How long an idle session lives (default `60`) |
| `LEAN_TIMEOUT` | Seconds before a Lean check times out (default `120`) |
| `FORMAL_SANDBOX` | `auto` (default), `bwrap` to require bubblewrap, or `off` |
| `FORMAL_WARM` | How many Lean processes keep Mathlib loaded: `on` or unset for one, a number for more, `off` for none |
| `ELAN_HOME` | Where the Lean toolchain lives (default `~/.elan`) |
| `FORMAL_HOME` | The root for everything below (default: the clone, or `~/.local/share/formal`) |
| `LEAN_PROJECT_DIR` | The Lean project that holds the toolchain pin and Mathlib |
| `FORMAL_RESULTS_DIR` | Where results are saved |
| `PROOF_CACHE_DIR` | Where accepted proofs are cached (default `$FORMAL_RESULTS_DIR/cache`) |
| `PROOF_CACHE_TTL_DAYS` | Age after which the next save deletes an entry (default `7`). `0` keeps nothing: each save deletes every entry |
| `XDG_DATA_HOME` | Used to find the default `FORMAL_HOME` outside a clone |
| `NO_COLOR` | Turns off colour in progress output |

An `.env` from before formal dropped its model pipeline lists keys that formal no longer
reads. `formal status` names them so you can delete them.

### Warm Lean

Most of a cold Lean check goes to loading Mathlib, not to checking the proof. So the
server keeps Lean processes with Mathlib already loaded, and sends them every proof they
can take. It starts them when the server starts, inside the same sandbox as any other Lean
run.

Measured on one machine (Mathlib v4.29.0, 20 cores):

| | Cold: a new Lean per check | Warm |
|---|---|---|
| Two simple proofs | 2.65 s | 20 to 25 ms |
| `exact?` premise search | 7.0 s every time | 5 s once, then about 25 ms |
| One `POST /check`: three proofs, one recovered | 13.9 to 16.7 s | 1.2 s (5.9 s on the first request) |

A warm process takes a proof only when its sole import is `import Mathlib`. Any other
proof runs cold, as before. Warm checks share a process, so code run by one proof could
write a false answer for the next. That is one more reason formal refuses proofs that can
run code. Every warm check starts from the same Mathlib environment, so declarations do
not carry over from one check to the next.

A warm process runs one check at a time. `FORMAL_WARM=3` keeps three, and each check
takes a free one. When all of them are busy, the check runs cold instead of waiting. In a
test with three requests at the same moment, one process sent one request cold (2.9 s).
Three processes kept all three warm (0.12 s or less).

- **Timeouts.** A check that runs past `LEAN_TIMEOUT` stops its process. A later check
  starts a new one.
- **Memory.** A warm process shows about 6.3 GB resident, but most of that is Mathlib's
  files, which all processes share. The first process takes about 600 MB of available
  memory, and each further process about 650 MB.
- **Replacement.** A process keeps about 300 KB for every check it runs, so formal
  replaces it after 1,000 checks.

`formal status` shows whether warm checking is on. Without the REPL, formal says so once
and checks everything cold. `formal setup` builds the REPL. For a Lean project that an
older formal created, setup first adds the REPL to `lakefile.toml`, at the tag that
matches the project's `lean-toolchain`. It changes nothing else and downloads nothing from
Mathlib.

### Proof cache

formal writes every proof that Lean accepted and the audit passed to disk, and reuses it.

**The key is what is being proved:** the function source, the property kind, and the
`formal` statement. formal normalises operator spelling and spacing, so
`∀ x, p x → q x` and `forall x, p x -> q x` count as one statement.

**The prose is left out of the key on purpose.** Descriptions, preconditions and
assumptions are English, and English varies between writers and between runs. With prose
in the key, every rephrasing meant a new key and a new proof of something already proved.
Across the 148 properties of a real run, the function, the kind and the statement
distinguished all of them. That is an observation about that corpus, not a theorem: the
distinctness of keys rests on SHA-256.

That choice has a cost: two callers can agree on a statement but model it differently.
So a cache hit reports the description and assumptions recorded with the proof. Read them. If that model is not yours, change the
`formal` statement so that it says what you mean.

formal caches only proofs that Lean accepted and the audit passed. It never caches a
failure, a proof that contains `sorry`, or a proof it refused. Cache entries from before
the axiom audit are not trusted: formal checks each one again on first use.

The cache holds one JSON file per entry under `PROOF_CACHE_DIR`. The next save deletes
entries older than `PROOF_CACHE_TTL_DAYS`. The cache only saves time: when a write fails,
formal logs it and the result stays the same.

### Sandbox

formal refuses proofs that can run code, but Lean itself remains a program that runs
input written by a model. So formal also runs Lean inside
[bubblewrap](https://github.com/containers/bubblewrap):

- **No network,** so a proof cannot send out anything it reads.
- **No home directory.** A temporary file system hides it, so `~/.claude`, `~/.ssh` and
  `~/.aws` stay invisible.
- **A read only root,** with the Lean toolchain mounted read only.
- **One writable directory,** `lean_project/`.

Install bubblewrap (`pacman -S bubblewrap`, `apt install bubblewrap`) to turn it on.
Without it, Lean runs outside a sandbox and formal warns once per run.
`FORMAL_SANDBOX=bwrap` makes a missing bubblewrap an error, and `off` turns the sandbox
off without a warning. `formal status` shows which one applies.

bubblewrap exists only on Linux. On macOS, Lean always runs outside a sandbox, formal
warns once per run, and `FORMAL_SANDBOX=bwrap` refuses to start Lean. Do not let an
untrusted agent send proofs to formal on macOS.

The sandbox costs nothing measurable: 3.19 s with it and 3.31 s without, for a cold proof
that imports Mathlib.

The server listens on localhost, and `POST /session/{id}/check` runs Lean that the caller
sent. Do not expose it beyond the loopback interface.

## Development

From `rust/`:

```sh
cargo +nightly fmt --all       # format: rustfmt.toml uses options only nightly has
cargo clippy --all-targets     # lint: clippy::pedantic is denied
cargo test                     # test
```

The code uses Rust edition 2024. The tests that need Lean skip themselves when there is
none, so `cargo test` is quick without Lean and thorough with it. Five suites need Lean:

```sh
cargo test -p formal-lean --test lean          # a true theorem, a false one, a hole, a batch
cargo test -p formal-lean --test audit         # the false theorems Lean accepts and formal must not
cargo test -p formal-lean --test warm          # a warm Lean gives the verdict a cold one gives
cargo test -p formal-lean --test confinement   # bubblewrap confines what it claims to
cargo test -p formal-lean --test guide_lemmas  # every lemma the guide names still exists
```

CI runs all five in its `lean` job, inside the sandbox, on every pull request and on every
push to `main`. The job fails before the tests if Lean or the REPL is missing, so no suite
can pass by skipping itself.

Three data files decide whether a change may land:

- `tests/conformance/golden/responses.json` pins the HTTP surface.
- `tests/fixtures/cache_keys.toml` pins the digest that files each cached proof.
- `tests/fixtures/hint_corpus.toml` pins every hint.

See `CLAUDE.md` for how to change them.

### Updating Lean dependencies

`lean_project/lake-manifest.json` pins the exact commit of Mathlib and of everything it
pulls in. `lakefile.toml` names a revision only for the direct dependencies, so the
manifest is what pins the rest. `formal setup` skips `lake update` whenever the manifest
exists.

To move to a newer Mathlib:

1. In `lakefile.toml`, bump both `rev` values. Mathlib and the REPL use the same Lean
   version tag.
2. Bump the version in `lean-toolchain`.
3. Regenerate the manifest and the build, then commit:

   ```sh
   cd lean_project
   lake update && lake exe cache get && lake build Warmup repl
   ```

Check a proof afterwards. A Mathlib update can break proofs that rely on lemma names or on
`simp` behaviour that changed.
