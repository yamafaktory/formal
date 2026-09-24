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

You need a Rust toolchain.

```sh
cargo install --git https://github.com/yamafaktory/formal formal-cli
formal setup
formal status
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

**The function.** `pricing.py`:

```python
def apply_discount(price, rate):
    rate = max(0.0, min(rate, 1.0))
    return price * (1 - rate)
```

**The property.** The agent adds it to `formal.properties.json` and commits the file:

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

**The session.** The agent opens a session on the spec file:

```sh
curl -s -X POST localhost:1337/session -H 'content-type: application/json' \
  -d '{"spec_file": "/abs/path/to/formal.properties.json"}'
```

```json
{ "session_id": "fb2c6e49…", "cached": [], "work": ["apply_discount/bounded"], "stale": [], "complete": false }
```

**A first proof.** The agent models the function over rationals and tries `linarith`:

```lean
import Mathlib

def applyDiscount (price rate : ℚ) : ℚ :=
  price * (1 - max 0 (min rate 1))

theorem apply_discount_bounded (price rate : ℚ) (h : 0 ≤ price) :
    0 ≤ applyDiscount price rate ∧ applyDiscount price rate ≤ price := by
  unfold applyDiscount
  constructor <;> linarith
```

```sh
curl -s -X POST localhost:1337/session/$SID/check -H 'content-type: application/json' \
  -d '{"proof_files": {"apply_discount/bounded": "/abs/path/to/proofs/discount.lean"}}'
```

```json
{
  "verified": [],
  "recovered": [],
  "failed": [{
    "id": "apply_discount/bounded",
    "error": "linarith failed to find a contradiction\ncase left.h\nprice rate : ℚ\nh : 0 ≤ price\na✝ : price * (1 - max 0 (min rate 1)) < 0\n⊢ False\nfailed",
    "line": 9, "col": 18,
    "hint": "The `linarith` tactic ran and failed to close the goal. `linarith` needs the goal and hypotheses to be linear arithmetic over an ordered field. Introduce the facts it should use as hypotheses first, or use `nlinarith` for products. …"
  }],
  "remaining": ["apply_discount/bounded"],
  "complete": false
}
```

formal first tried to recover the proof on its own, and failed. The error shows the goal
Lean could not close. It is nonlinear: it multiplies `price` by a term in `rate`, and
`linarith` decides only linear arithmetic. The hint says so, and names the two ways out:
state the needed facts as hypotheses, or use `nlinarith`.

**The fix.** The agent states the bounds on the clamped rate as hypotheses, and switches
to `nlinarith`, which multiplies hypotheses together and so reaches nonlinear goals:

```lean
  unfold applyDiscount
  have lo : 0 ≤ max 0 (min rate 1) := le_max_left _ _
  have hi : max 0 (min rate 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
  constructor <;> nlinarith
```

```json
{ "verified": ["apply_discount/bounded"], "recovered": [], "failed": [], "remaining": [], "complete": true }
```

This check took 0.24 s, because the server keeps Mathlib loaded.

**Next time.** formal stores the accepted proof. A later session on the same spec file
finds it, and reports what was proved:

```json
{
  "cached": [{
    "id": "apply_discount/bounded",
    "description": "a discounted price is never negative and never above the original price",
    "kind": "invariant",
    "assumptions": ["prices and rates modelled as rationals, not floats"]
  }],
  "work": [], "stale": [], "complete": true
}
```

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
POST /session/{id}/check         {"proofs": {"<id>": "<lean>"}} or {"proof_files": {"<id>": "<path>"}}
     → {verified, recovered, failed, remaining, complete}
     fix the failures, send only those ids again, repeat
```

Three things keep the loop cheap:

- **Properties are registered once.** A retry sends only the corrected Lean.
- **A failure comes back short.** formal returns the first error and a hint, never Lean's
  full output, which for a Mathlib failure runs to thousands of tokens.
- **formal recovers what it can.** Before it reports a failure, it replaces the proof
  with an automatic tactic chain (`rfl`, `omega`, `norm_num`, `linarith`, `ring`,
  `decide`, `simp`), then with a premise search (`exact?`). A proof recovered this way
  appears under `recovered` and never goes back to the agent.

### The spec file

Properties live in a JSON file that you commit next to the code. The
[worked example](#a-worked-example) shows one entry. `id`, `function`, `kind` and
`formal` are required. formal resolves `source_file` against the spec file's directory,
or against `root` when you pass one. Send `spec_file` as an absolute path: the server
resolves it, and its working directory is not yours.

**Commit the file.** The cache depends on it. Two independent runs over one small function
produced six and seven properties. They agreed on the wording of none of them, and stated
one of them in opposite directions. A cache cannot match properties that change on every
run. A committed file is the same every time, so a proof is written once and reused.

A committed file is also reviewable. It shows what was checked last week, and a diff
shows when the answer changes.

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

formal checks itself. `formal.properties.json` in this repository is formal's own spec,
with the proofs in `proofs/`. Two of its properties guard against collisions that really
happened in formal's cache key: an operator spelled as a word counts only at a word
boundary, and no field of the key can imitate the boundary between two others.

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
- **It audits the axiomatic dependencies of every declaration.** formal appends a command
  to the proof. The command lists every declaration that depends, directly or through
  other declarations in the file, on an axiom other than `propext`, `Classical.choice`
  and `Quot.sound`. A declared axiom, a `sorry` (`sorryAx`) or `native_decide` fails the
  check at the line of that declaration. This also catches a `sorry` whose warning
  `#guard_msgs` suppresses.
- **It requires the audit to report.** The report carries a random nonce that the proof
  cannot know. If no report comes back, the check fails. This happens when elaboration
  stops before the end of the file, for example at an unclosed comment.

The audit takes imported Mathlib declarations as built, the same trust Lean extends to
them. It costs about 0.27 s on a cold check, and nothing measurable on a warm one.

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
| `GET /guide/{extract\|formalize\|tactics}` | The instructions for one phase |
| `POST /session` | `{"spec_file": path, "root"?: path}`, or `{"properties": [...]}` |
| `GET /session/{id}` | The current state of a session |
| `POST /session/{id}/check` | `{"proofs": {id: lean}}`, or `{"proof_files": {id: path}}` |
| `GET /session/{id}/proof/{property_id}` | The proof Lean accepted for one property |
| `DELETE /session/{id}` | Close a session early |

A session expires after `SESSION_TTL_MINUTES` of inactivity (default 60). Inline
`properties` suit a one off check, but nothing carries over to a later run. Paths in
`proof_files` must be absolute, like `spec_file`.

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
So a cache hit reports the description and assumptions recorded with the proof, as in the
[worked example](#a-worked-example). Read them. If that model is not yours, change the
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
