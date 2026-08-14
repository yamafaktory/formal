# formal

[![Checks](https://github.com/yamafaktory/formal/actions/workflows/checks.yml/badge.svg)](https://github.com/yamafaktory/formal/actions/workflows/checks.yml)

**Property checker for code, backed by Lean 4 and Mathlib. Your agent writes the
properties and the proofs; formal checks them.**

State a property about a pure function — that splitting preserves line count, that a
discount stays between 0 and 1 — as a Lean 4 theorem. formal checks it against Mathlib
and tells you whether it holds. What Lean accepts is mechanically verified, within the
limits described below.

**formal does not call a model.** No API key, no backend setting, no opinion about which
model you use. The agent already reading your code writes the properties and the Lean;
formal runs Lean over them in one batched invocation, recovers the failures it can
without help — auto-tactics, then a Mathlib premise search — remembers every proof Lean
accepted, and tells you when the code moves out from under a property.

That split is the whole design. An agent that can write Lean does not need a second model
started on its behalf to do it.

## What this actually is

Three judgements happen before Lean ever runs, and the agent makes all three:

1. **Decomposition** — which parts of the code are pure functions
2. **Property extraction** — what those functions should satisfy, with explicit
   preconditions and modelling assumptions
3. **Formalization** — the Lean 4 theorem that says so

Only then does Lean check the proof. Lean is mechanically sound — it cannot be fooled —
but it only checks what it is given. If those three judgements misread your function, or
produced a property that is technically true but misses the point, Lean will happily
prove the wrong thing. `GET /guide` serves the instructions formal has for making them
well; it cannot make them for you.

**What "verified" means here:** Lean accepted a proof of a theorem someone derived from
your code. That is a meaningful signal — LLMs make logical errors and Lean catches them —
but it is not equivalent to a certified compiler or a formal proof that your source is
correct.

**Useful for:**
- Catching logical errors in generated code that tests might miss
- Surfacing the assumptions made about your code, stated explicitly
- Confidence in pure domain logic: calculations, transformations, validations
- A machine-checked, reviewable record of what holds under which assumptions

**Does not give you:**
- A guarantee your source is correct — only that a Lean model of it satisfies the stated properties
- Complete coverage — whoever writes the properties chooses them, and may miss important ones
- Traditional formal verification — that needs a certified translation from source to proof, which this does not have

Side effects (DB calls, HTTP, I/O) are excluded by design. Properties that depend on
reference equality, reflection or runtime behaviour are classified `unverifiable` — a
modelling limit, not a bug and not a failure.

## Setup

Requires a Rust toolchain.

```sh
cargo install --git https://github.com/yamafaktory/formal formal-cli
formal setup
```

No clone needed — the Lean project is bundled in the binary and created under
`~/.local/share/formal` on first run, which is also where Mathlib's oleans land.

Working on formal itself? Clone it, and a binary built from the checkout keeps its
Lean project and results inside the repo.

`formal setup` installs [elan](https://github.com/leanprover/elan) and the pinned Lean
toolchain, then downloads prebuilt Mathlib oleans. That is all it does — there is no
backend to configure. Re-running is safe: completed steps are skipped.

Any elan already on your system is used as-is. Nothing is added to your shell
configuration — formal locates the toolchain under `ELAN_HOME` (default `~/.elan`)
itself. See [lean-lang.org/install](https://lean-lang.org/install/).

Then check it:

```sh
formal status
```

## Driving formal from an agent

formal exposes an HTTP API. The agent reads your code, states the properties, writes the
Lean, and formal checks it. Nothing else is started.

Start the server once — the command is safe to run before every request, since it
returns immediately when one is already up:

```sh
formal serve --background     # detaches, returns when /health answers
formal status                 # …  server  http://127.0.0.1:1337 (running)
formal stop
```

### The loop

```
GET  /guide                      the workflow and the spec-file schema (~650 tokens)
GET  /guide/extract              how to find pure functions and properties
     → write formal.properties.json, commit it
POST /session {"spec_file": …}   → {cached, work, stale}
GET  /guide/formalize            Lean 4 conventions for stating a property
GET  /guide/tactics              rules that prevent the common proof failures
POST /session/{id}/check         {"proofs": {"<id>": "<lean>"}}
     → {verified, failed: [{id, error, line, col, hint}], remaining, complete}
     fix the failures, resubmit only those ids, repeat
```

The guide is served in stages rather than as one document, so an agent pays for the Lean
conventions only once it is actually writing Lean. `tactics` is the accumulated list of
what goes wrong — never adding a tactic after `simp`, `decide` rather than `omega` for
string-literal lengths, how to close an `Except.ok = Except.error` branch. Most
first-attempt failures are on it.

Three things keep the loop cheap. Properties are registered once, so a retry carries only
the corrected Lean and not the metadata again. Every proof in a request is checked in a
single Lean invocation, so a batch pays one `import Mathlib` rather than one per proof.
And a failure comes back as its first error plus a targeted hint — never the full Lean
output, which for a Mathlib failure runs to thousands of tokens of noise.

Before a failure is reported at all, formal tries to close it without a model: the
auto-tactic chain first, then a Mathlib premise search for a lemma that discharges the
goal. Proofs recovered that way never reach the agent.

### The spec file

Properties live in a JSON file you commit alongside the code:

```json
{
  "version": 1,
  "properties": [
    {
      "id": "split_imports/conservation",
      "function": "split_imports",
      "kind": "invariant",
      "formal": "forall ls, length (fst (partition ls)) + length (snd (partition ls)) = length ls",
      "description": "splitting preserves the number of lines",
      "preconditions": [],
      "assumptions": ["text modelled as List String, one element per line"],
      "source_file": "rust/formal-lean/src/verifier.rs",
      "function_code": "fn split_imports(lean_code: &str) -> ..."
    }
  ]
}
```

`id`, `function`, `kind` and `formal` are required. `source_file` is resolved relative to
the spec file unless you pass `root`. The `spec_file` path itself must be absolute: the
server resolves it, and its working directory is not the caller's.

**Commit it.** That is not a filing preference — it is what makes the cache work. Two
independent extraction runs over one small function produced six and seven properties,
agreed on the wording of none of them, and stated one of them in opposite directions.
Nothing re-derived each run can hit a cache. A committed file is the same bytes every
time, so a proof is written once and reused forever.

It also makes the claim reviewable. A verification tool whose properties are re-invented
on every run cannot tell you what it checked last week, and cannot show you a diff when
the answer changes.

### formal's own properties

`formal.properties.json` in this repository is formal's own spec, with the proofs in
`proofs/`. Three properties so far, two of them guarding collisions that were real: that
a word-spelled operator is only an operator on a word boundary, and that no field of the
cache payload can imitate the boundary between two others. Both were found by pointing
formal at its own key derivation.

### Staleness

The risk a committed spec introduces is outliving its code. Each property records the
function source it was written against; if that source has since changed, the property is
reported as `stale` and never proved:

```json
{ "work": [], "cached": [], "stale": ["split_imports/conservation"], "complete": false }
```

Proving a property against code it no longer describes yields a true theorem about
nothing, so formal declines to. Re-read the function, update the property and its
`function_code`, and the session goes green again. `complete` is false while anything is
stale.

Comparison is normalised text rather than a parse, so it works for every language formal
accepts, and reindentation is not a change. A property with no `source_file` cannot go
stale — there is nothing recorded to compare against.

### Add this to your agent's instructions

For Claude Code, add to `CLAUDE.md`; for other agents, the equivalent file.

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

## API reference

`formal serve` binds `127.0.0.1:1337` by default (`FORMAL_HOST`, `FORMAL_PORT`).

| Endpoint | Purpose |
|---|---|
| `GET /guide` | Workflow, spec-file schema, topic list |
| `GET /guide/{extract\|formalize\|tactics}` | Instructions for one phase |
| `POST /session` | `{"spec_file": path, "root"?: path}` or `{"properties": [...]}` |
| `GET /session/{id}` | Current state |
| `POST /session/{id}/check` | `{"proofs": {id: lean}}` |
| `DELETE /session/{id}` | Close early |

```sh
curl -X POST localhost:1337/session -H 'content-type: application/json' \
  -d '{"spec_file": "/abs/path/to/formal.properties.json"}'
```

```json
{
  "session_id": "7577b934…",
  "cached": [{"id": "…", "description": "…", "kind": "…", "assumptions": ["…"]}],
  "work": ["split_imports/conservation"],
  "stale": [],
  "complete": false
}
```

A cache hit reports what was actually proved, not what you asked for — see
[Proof cache](#proof-cache) for why that distinction matters.

```sh
curl -X POST localhost:1337/session/$SID/check -H 'content-type: application/json' \
  -d '{"proofs": {"split_imports/conservation": "import Mathlib\ntheorem …"}}'
```

```json
{
  "verified": ["split_imports/conservation"],
  "failed": [{"id": "…", "error": "unknown identifier 'foo'", "line": 4, "col": 2, "hint": "…"}],
  "remaining": [],
  "complete": true
}
```

Sessions expire after `SESSION_TTL_MINUTES` (default 60). Passing `properties` inline
instead of `spec_file` works for ad-hoc use, but nothing is reusable across runs.

## Configuration

Set in `.env` (created by `formal setup`), overridable by environment variable.
`formal status` prints the resolved values and flags any key nothing reads.

| Variable | Description |
|---|---|
| `FORMAL_HOST` | Server bind address (default `127.0.0.1`) |
| `FORMAL_PORT` | Server port (default `1337`) |
| `SESSION_TTL_MINUTES` | Idle lifetime of a proof session (default `60`) |
| `LEAN_TIMEOUT` | Seconds before a Lean check times out (default `120`) |
| `FORMAL_SANDBOX` | `auto` (default), `bwrap` (require it), or `off` |
| `ELAN_HOME` | Lean toolchain install (default `~/.elan`) |
| `FORMAL_HOME` | Root for everything below (default: the checkout) |
| `LEAN_PROJECT_DIR` | Lean project holding the toolchain and Mathlib |
| `FORMAL_RESULTS_DIR` | Directory for saved results |
| `PROOF_CACHE_DIR` | Cached proofs (default `$FORMAL_RESULTS_DIR/cache`) |
| `PROOF_CACHE_TTL_DAYS` | Entries older than this are deleted on the next save (default `7`, `0` disables) |
| `XDG_DATA_HOME` | Honoured when resolving the default `FORMAL_HOME` outside a checkout |
| `NO_COLOR` | Honoured — suppresses colour in progress output |

An `.env` left over from before the LLM pipeline was removed will list keys formal no
longer reads; `formal status` names them so they can be deleted.

## Proof cache

A proof Lean accepted is written to disk and reused. Both paths share one cache: a proof
an agent wrote is a hit for a later autonomous run, and the reverse.

**The key is what is being proved** — the function source, the property kind, and the
formal statement, with operator spelling and spacing normalised so `∀ x, p x → q x` and
`forall x, p x -> q x` are one statement.

**The prose is deliberately not in the key.** Descriptions, preconditions and assumptions
are English, and English varies between writers and between runs; keying on it meant
every rephrasing was a fresh key and a re-proof of something already proved. Across the
148 properties from a real run, the function, kind and formal statement separate all of
them.

The cost of that choice is that two callers can agree on a statement while modelling it
differently. So a cache hit reports the description and assumptions recorded when the
proof was accepted:

```json
{"id": "…", "description": "splitting preserves the line count",
 "assumptions": ["text modelled as List String"]}
```

Read them. If that modelling is not yours, the hit is not the property you meant, and you
should change the formal statement so it says so.

Only proofs Lean actually accepted are cached — a verdict with no Lean run behind it, a
proof still containing `sorry`, or text that does not parse as Lean is refused and
logged. Failures are never cached; they always go through the full retry loop.

One JSON file per entry under `PROOF_CACHE_DIR`. Entries older than
`PROOF_CACHE_TTL_DAYS` are deleted on the next save. The cache is strictly an
optimisation: if it cannot be written, the failure is logged and the result is unaffected.

## Checking the formalization

Lean guarantees the theorem it was given is true. It cannot tell you whether that theorem
is the property you wanted — if formalization misread your code, Lean proves the wrong
thing and reports success. That is the failure this tool is least able to notice, because
it looks exactly like a pass.

formal used to do this itself, reading each proved theorem back into English *without
showing the model the original description* and comparing the two:

```
  ✓ [bound] discount is always between 0 and 1
      ⚠ theorem may not match this property: the hypothesis assumes the
        conclusion, so it holds for any definition of the function
        Lean theorem states: for any rational d, if 0 ≤ d ≤ 1 then 0 ≤ d ≤ 1
```

That check went with the pipeline, and nothing replaces it. It is now yours to do: read
the theorem you wrote and ask whether it says what the property says.

Be aware of what you lose. The removed check was *blinded* — it back-translated without
seeing the original description, so the comparison was between two independent readings.
An agent checking its own translation has already seen both, and cannot un-see them. That
is weaker, and it is the one capability full inversion cost outright.

## Sandboxing

Lean is not a passive checker: elaboration can execute arbitrary code through `#eval`,
macros and `initialize` blocks. Since the code being elaborated was written by a model,
proofs are checked inside [bubblewrap](https://github.com/containers/bubblewrap):

- No network — `--unshare-net`, so a proof cannot exfiltrate anything it reads
- No home directory — masked by a tmpfs, so `~/.claude`, `~/.ssh` and `~/.aws` are invisible
- Read-only root, with the Lean toolchain bound read-only
- Nothing writable except `lean_project/`

Install bubblewrap (`pacman -S bubblewrap`, `apt install bubblewrap`) to enable it.
Without it Lean runs unsandboxed and warns once per run; `FORMAL_SANDBOX=bwrap` makes its
absence a hard error, `off` opts out silently. `formal status` shows which applies.

Measured cost of sandboxing: none — 3.19s sandboxed against 3.31s unsandboxed for a proof
importing Mathlib.

The server binds to localhost and `POST /session/{id}/check` runs caller-supplied Lean.
Do not expose it beyond the loopback interface.

## Limitations

- **The agent decides what is checked.** It can misread code, miss properties, or produce
  theorems that are true but irrelevant. Lean only checks what it is given, and formal has
  no second opinion to offer — it does not run a model.
- **No blinded fidelity check.** An agent verifying that its own theorem matches its own
  property has seen both. See [Checking the formalization](#checking-the-formalization).
- **Preconditions and assumptions may be wrong.** A proof built on a wrong assumption is
  not evidence your code is correct.
- **Pure logic only.** Side effects are excluded by design.
- **Modelling limits.** Floats are modelled as rationals; strings use structural equality.
  IEEE 754 precision and reference semantics cannot be modelled.
- **Not a test replacement.** This checks properties for all inputs under stated
  assumptions; it does not replace integration or end-to-end tests.
- **Lean timeouts.** Complex proofs may time out — raise `LEAN_TIMEOUT`.
- **First install is large.** Mathlib's prebuilt oleans are several GB and take a few
  minutes, once, during `formal setup`.

## Development

From `rust/`:

```sh
cargo fmt --all           # format (needs a nightly rustfmt)
cargo clippy --all-targets  # lint
cargo test                # tests
```

Edition 2024, `clippy::pedantic` denied. The tests that need Lean do nothing when
there is none, so `cargo test` is quick without a toolchain and thorough with one —
`--test lean` checks proofs, `--test guide_lemmas` checks that every lemma this
guide names still exists in Mathlib.

What decides whether a change may land is data, not code:
`tests/conformance/golden/responses.json` for the HTTP surface,
`tests/fixtures/cache_keys.toml` for the digests every cached proof is filed
under, and `tests/fixtures/hint_corpus.toml` for the advice. See CLAUDE.md.

### Updating Lean dependencies

`lean_project/lake-manifest.json` pins the exact commit of Mathlib and everything it pulls
in — `lakefile.toml` only names a revision for Mathlib itself, so inherited packages are
unpinned without it. `formal setup` skips `lake update` whenever the manifest exists.

To move to a newer Mathlib, bump `rev` in `lakefile.toml` and the version in
`lean-toolchain`, then regenerate and commit:

```sh
cd lean_project
lake update && lake exe cache get && lake build Warmup
```

Verify a file afterwards — a Mathlib bump can invalidate proofs that relied on lemma names
or `simp` behaviour that changed.
