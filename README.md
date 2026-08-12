# formal

[![Checks](https://github.com/yamafaktory/formal/actions/workflows/checks.yml/badge.svg)](https://github.com/yamafaktory/formal/actions/workflows/checks.yml)

An LLM-driven property checker for code, backed by Lean 4 as a proof engine.

Point it at a file, and it will: identify pure functions, generate properties those
functions should satisfy, translate them into Lean 4 theorems, and attempt to prove
them with Mathlib. Properties that Lean accepts are mechanically verified — but only
within the limits described below.

Works with any LLM backend — Claude, GPT-4, Gemini, Llama, Mistral, or any OpenAI-compatible endpoint.

## What this actually is

The pipeline has three LLM steps before Lean ever runs:

1. **Decomposition** — the LLM reads your code and identifies which parts are pure functions
2. **Property extraction** — the LLM generates properties it believes those functions satisfy, along with explicit preconditions and modeling assumptions
3. **Formalization** — the LLM translates each property into a Lean 4 theorem

Only then does Lean check the proof. Lean is mechanically sound — it cannot be fooled — but it only checks what it is given. If the LLM misunderstood your function, or generated a property that is technically true but misses the point, Lean will happily prove the wrong thing.

**What "verified" means here:** Lean accepted a proof of a theorem that the LLM derived from your code. This is a meaningful signal — LLMs make logical errors and Lean catches them — but it is not equivalent to a certified compiler or a formal proof that your source code is correct.

**What this is useful for:**
- Catching logical errors in AI-generated code that tests might miss
- Surfacing the assumptions an LLM makes about your code (now shown explicitly)
- Increasing confidence in pure domain logic: calculations, transformations, validations
- Getting a structured, machine-checked view of what properties hold under stated assumptions

**What this does not give you:**
- A guarantee that your source code is correct — only that a Lean model of it satisfies generated properties
- Complete coverage — the LLM picks which properties to check and may miss important ones
- Traditional formal verification — that requires a certified translation from source to proof, which this does not have

## How it works

```
Your code (any language)
  → LLM: extract pure functions, identify side effects
  → LLM: generate properties with explicit preconditions and assumptions
  → LLM: translate each property into a Lean 4 theorem + proof
  → Lean 4 + Mathlib: accept or reject each proof (with retries)
  → Results: verified / failed / unverifiable / error
```

Side effects (DB calls, HTTP, I/O) are excluded — only pure, deterministic logic is
checked. Properties that depend on reference equality, reflection, or runtime behaviour
are classified as `unverifiable` (not a bug, not a failure — a modeling limit).

Every property now carries explicit **preconditions** (what must hold on inputs) and
**assumptions** (modeling choices made during translation). These are shown in the
output so you can judge whether the LLM's interpretation matches your intent.

## Setup

Requires [uv](https://docs.astral.sh/uv/getting-started/installation/). Install the
command, then let it install everything else:

```sh
uv tool install git+https://github.com/yamafaktory/formal
formal setup
```

No clone needed — the Lean project is bundled in the wheel and created under
`~/.local/share/formal` on first run, which is also where Mathlib's oleans land.

Working on formal itself? Clone it and run `./formal setup` instead; a checkout
keeps its Lean project and results inside the repo.

`formal setup` installs [elan](https://github.com/leanprover/elan) and the pinned
Lean toolchain, downloads prebuilt Mathlib oleans, and then asks which LLM backend
to use. Re-running it is safe: steps that are already done are skipped. Use
`--lean-only` or `--backend-only` to run just one half.

Any elan already on your system is used as-is, however you installed it — so if
your package manager carries it, use that and `formal setup` will pick it up and
install the pinned Lean version into it. Otherwise it offers elan's official
installer. See [lean-lang.org/install](https://lean-lang.org/install/).

Nothing is added to your shell configuration — `formal` locates the Lean
toolchain under `ELAN_HOME` (default `~/.elan`) by itself.

Two backends:

**1 — Claude Code CLI** (uses your local `claude` binary and Pro/Max plan, no API key needed)

**2 — OpenAI-compatible API** (any provider with an OpenAI-compatible endpoint):

| Provider | Base URL |
|---|---|
| OpenAI | `https://api.openai.com/v1` |
| Anthropic | `https://api.anthropic.com/v1` |
| Groq | `https://api.groq.com/openai/v1` |
| Ollama (local) | `http://localhost:11434/v1` |
| LM Studio | `http://localhost:1234/v1` |
| Any other | Any OpenAI-compatible endpoint |

Settings are written to `.env`. Available models are fetched from `/v1/models`; if
unsupported, enter the model name manually.

Then check the installation:

```sh
./formal status
```

Optionally put `formal` on your `PATH` for use from any directory:

```sh
uv tool install .
```

### Add this to your project's AI agent instructions

For Claude Code, add to your `CLAUDE.md`. For Cursor, Copilot, or other agents, add
to the equivalent instructions file.

````markdown
## Formal Verification

After implementing any feature that contains non-trivial pure logic (calculations,
transformations, validations, business rules), verify it:

```sh
~/dev/formal/formal verify path/to/file.java
```

**When to verify:** after writing or modifying pure domain logic — pricing
calculations, volume computations, data transformations, validation functions.

**When to skip:** pure I/O code, controller wiring, configuration, tests.

Results:
- `full` — all properties proved under stated assumptions
- `partial` / `failed` — investigate unverified properties; may indicate a logic bug
- `unverifiable` — modeling limitation (reference equality, reflection, etc.), not a bug
- `error` — the checker itself failed; no verdict was reached, so re-run rather than changing code

Review the preconditions and assumptions in the output. If they do not match your
intent, the proof result may not reflect real behaviour.
````

## CLI

The `formal` script is the primary interface — it runs the pipeline in-process,
no daemon involved.

```sh
# Verify a file (language auto-detected from extension)
./formal verify path/to/Feature.java

# Verify inline code
./formal verify --code 'def f(x): return max(0, x)' --lang Python

# Full JSON result
./formal verify path/to/Feature.java --json

# Verify properties one at a time instead of in parallel
./formal verify path/to/Feature.java --no-parallel

# Show resolved paths, toolchain state and LLM backend
./formal status

# Re-run installation and backend configuration
./formal setup

# Serve the HTTP API on 127.0.0.1:1337
./formal serve
```

`verify` exit codes, so it can gate a commit hook or CI step:

| Code | Meaning |
|---|---|
| `0` | Every verifiable property was proved |
| `1` | At least one property was not proved — investigate |
| `2` | formal itself failed; no verdict was reached |
| `3` | No pure logic found, so nothing was checked |

`3` is distinct from `0` deliberately: a file that was never checked should not
look like a file that passed. Decomposition is an LLM step and can miss functions
it found on a previous run, so treat `3` on a file you expect to have pure logic
as a signal to re-run rather than as a pass.

### Progress output

Progress streams to stderr while the run happens, so the result on stdout stays
pipeable:

```
[PIPELINE] Decomposing feature [Java]: SomeService.java
[PIPELINE] Pure functions: ['computePrice', 'applyDiscount']
[PIPELINE] Extracted 5 properties
[SCREEN  ] ✓ prop_1: VERIFIABLE — discount is always between 0 and 1
[SCREEN  ] ~ prop_3: UNVERIFIABLE — depends on reference equality
[CACHE   ] prop_1 [bound] cache hit — skipping proof
[VERIFY  ] prop_2 [monotonicity] Formalizing: higher discount yields lower price
[LEAN    ] prop_2 theorem: import Mathlib ...
[VERIFY  ] prop_2 generating proof (attempt 1/3)...
[FAIL    ] prop_2 ✗ attempt 1 failed: type mismatch
[VERIFY  ] prop_2 generating proof (attempt 2/3)...
[OK      ] prop_2 ✓ verified
[PIPELINE] Done — verified: 4, failed: 0, unverifiable: 1
```

### Verify output

```
─────────────────────────────────────────
File:    path/to/Feature.java
Summary: Applies discount and computes final price
Score:   full  (4/5 verified, 1 unverifiable)
Pure functions: computePrice, applyDiscount
Impure parts: 2 side effects (not verifiable)
─────────────────────────────────────────
  ✓ [bound] discount is always between 0 and 1
      Preconditions: discount is a float
      Assumptions:   floats modeled as rationals, no NaN or Inf
  ✓ [monotonicity] higher discount yields lower price
      Preconditions: price > 0, 0 <= discount <= 1
      Assumptions:   floats modeled as rationals
  ~ [invariant] bundleId reference matches stored entity
      → depends on JVM reference equality, not structural equality
─────────────────────────────────────────
```

Preconditions and assumptions are shown for every property so you can verify that
the LLM's interpretation of your code matches what you intended.

## API reference

The HTTP API is optional — start it with `./formal serve` (127.0.0.1:1337 by
default). It exists for clients that cannot shell out, such as an agent running in
a sandbox without Lean installed.

### `POST /verify-feature`

```sh
# From a file (language auto-detected)
curl -X POST http://localhost:1337/verify-feature \
  -H 'Content-Type: application/json' \
  -d '{"file": "/absolute/path/to/Feature.java"}'

# Inline code
curl -X POST http://localhost:1337/verify-feature \
  -H 'Content-Type: application/json' \
  -d '{"code": "...", "language": "TypeScript"}'
```

Supported languages: Python, Java, Kotlin, TypeScript, JavaScript, Go, Rust, C#, C++, Ruby.

**Response:**

```json
{
  "overall_score": "full | partial | failed | no_pure_logic",
  "properties_found": 5,
  "properties_verified": 4,
  "properties_unverifiable": 1,
  "pure_functions": ["computePrice", "applyDiscount"],
  "impure_parts": ["saves to DB", "sends email"],
  "results": [
    {
      "property_id": "prop_1",
      "description": "discount is always between 0 and 1",
      "kind": "bound",
      "status": "verified",
      "verified": true,
      "preconditions": ["discount is a float"],
      "assumptions": ["floats modeled as rationals", "no NaN or Inf"],
      "lean_code": "...",
      "lean_output": "...",
      "retries": 0,
      "reason": ""
    }
  ]
}
```

**Scores** (computed over verifiable properties only, unverifiable excluded):

| Score | Meaning |
|---|---|
| `full` | Every property was checked and proved |
| `partial` | ≥50% of checked properties proved, or something could not be checked |
| `failed` | <50% of verifiable properties proved |
| `no_pure_logic` | No pure functions found |
| `error` | Nothing could be checked — formal itself failed, no verdict was reached |

**Property status:**

| Status | Meaning |
|---|---|
| `verified` | Lean 4 accepted the proof under stated preconditions and assumptions |
| `failed` | Proof could not be found — may indicate a logic bug or a bad translation |
| `unverifiable` | Property cannot be modelled in Lean 4 (not a bug) |
| `error` | formal failed while checking this property — a tool failure, not a verdict about your code |

### `POST /verify`

Generates Python code for a natural language task and verifies it end-to-end.

```sh
curl -X POST http://localhost:1337/verify \
  -H 'Content-Type: application/json' \
  -d '{"task": "a function that computes compound interest"}'
```

### `GET /health`

```sh
curl http://localhost:1337/health
```

## Configuration

Set in `.env` (created by `formal setup`), overridable via environment variables:

| Variable | Description |
|---|---|
| `LLM_BACKEND` | `claude-cli` or `openai` (set by `formal setup`) |
| `CLAUDE_CONFIG_DIR` | Claude config directory (default: `~/.claude`). Use this to select a different account, e.g. `~/.claude-work`. |
| `LLM_BASE_URL` | Base URL of any OpenAI-compatible endpoint |
| `LLM_API_KEY` | API key (leave empty for local models) |
| `LLM_MODEL` | Model name as accepted by the provider |
| `LLM_TEMPERATURE` | Sampling temperature for the OpenAI backend (default: `0`, for repeatable decomposition). Leave blank to omit the parameter for models that reject it. |
| `MAX_PROOF_RETRIES` | Retry attempts per property on Lean errors (default: `3`) |
| `MAX_PARALLEL_PROPERTIES` | Concurrent property verifications (default: `4`) |
| `LEAN_TIMEOUT` | Seconds before a Lean check times out (default: `120`) |
| `LLM_TIMEOUT` | Seconds before an LLM call times out (default: `480`). Large files need more, especially when verifying several in parallel. |
| `FORMAL_SANDBOX` | `auto` (default, sandbox if bubblewrap is installed), `bwrap` (require it), or `off` |
| `ELAN_HOME` | Lean toolchain install (default: `~/.elan`). `formal` finds `lake` and `lean` here itself — no shell PATH setup needed. |
| `FORMAL_HOME` | Root for everything below (default: the checkout) |
| `LEAN_PROJECT_DIR` | Lean project holding the toolchain and Mathlib (default: `$FORMAL_HOME/lean_project`) |
| `FORMAL_RESULTS_DIR` | Directory for saved results (default: `$FORMAL_HOME/results`) |
| `PROOF_CACHE_DIR` | Directory for cached proof results (default: `$FORMAL_RESULTS_DIR/cache`) |
| `PROOF_CACHE_TTL_DAYS` | Cache entries older than this are deleted on the next save (default: `7`) |

`./formal status` prints the resolved values.

## Development

### Linting and formatting

[Ruff](https://docs.astral.sh/ruff/) handles both linting and formatting. Config is in `pyproject.toml`.

```sh
uv run ruff check .          # lint
uv run ruff check --fix .    # lint + auto-fix
uv run ruff format .         # format
```

Enabled rule sets: `E` (pycodestyle), `F` (pyflakes), `I` (isort), `UP` (pyupgrade). Line length: 120.

### Tests

```sh
uv run pytest --tb=short
```

### Updating Lean dependencies

`lean_project/lake-manifest.json` pins the exact commit of Mathlib and everything
it pulls in — `lakefile.toml` only names a revision for Mathlib itself, so
inherited packages are unpinned without it. `formal setup` therefore skips
`lake update` whenever the manifest exists, and installs from the pinned set.

To move to a newer Mathlib, bump `rev` in `lakefile.toml` and the version in
`lean-toolchain`, then regenerate and commit the result:

```sh
cd lean_project
lake update && lake exe cache get && lake build Warmup
```

Verify a file afterwards — a Mathlib bump can invalidate proofs that relied on
lemma names or `simp` behaviour that changed.

## Sandboxing

Lean is not a passive checker: elaboration can execute arbitrary code through
`#eval`, macros and `initialize` blocks. Since the code being elaborated was
written by an LLM, proofs are checked inside
[bubblewrap](https://github.com/containers/bubblewrap):

- No network — `--unshare-net`, so a proof cannot exfiltrate anything it reads
- No home directory — masked by a tmpfs, so `~/.claude`, `~/.ssh` and `~/.aws`
  are not visible
- Read-only root, with the Lean toolchain bound read-only
- Nothing writable except `lean_project/`

Install bubblewrap (`pacman -S bubblewrap`, `apt install bubblewrap`) to enable
it. Without it, Lean runs unsandboxed and a warning is printed once per run; set
`FORMAL_SANDBOX=bwrap` to make its absence a hard error instead, or
`FORMAL_SANDBOX=off` to opt out silently. `./formal status` shows which applies.

The LLM call itself is not sandboxed — it needs the network and, for the
`claude-cli` backend, your credentials.

## Proof cache

Successfully verified proofs are cached to disk. The same property on the same
function is never re-proved — on subsequent runs a `[CACHE]` hit is logged and
the stored result is returned immediately.

The cache key is a SHA-256 hash of the function source code, property description,
kind, formal spec, preconditions, and assumptions. Any change to these inputs
produces a new key; the old entry becomes an orphan and will be cleaned up by
the TTL eviction.

Only successful proofs are cached; failed attempts always go through the full
LLM + retry loop.

Cache files are written to `results/cache/` in the checkout (one JSON file per entry). Entries
older than `PROOF_CACHE_TTL_DAYS` (default: 7) are deleted automatically on the
next save. Set to `0` to disable the TTL. Override the directory with `PROOF_CACHE_DIR`.

The cache is strictly an optimisation. If it cannot be written — wrong
permissions, full disk — the failure is logged under `[CACHE]` and the
verification result is unaffected.

## Limitations

- **LLM-driven semantics.** Property extraction, formalization, and proof generation
  all go through an LLM. The LLM can misread code, miss properties, or generate
  theorems that are true but irrelevant. Lean only checks what it is given.
- **Preconditions and assumptions may be wrong.** Review them in the output. A proof
  built on a wrong assumption is not evidence that your code is correct.
- **Pure logic only.** Side effects (DB, HTTP, I/O) are excluded by design.
- **Modeling limits.** Floats are modelled as rationals; strings use structural
  equality. IEEE 754 precision and reference semantics cannot be modelled.
- **Not a test replacement.** This checks properties for all inputs under stated
  assumptions; it does not replace integration or end-to-end tests.
- **Lean timeout.** Complex proofs may time out — increase `LEAN_TIMEOUT` if needed.
- **First install is large.** Mathlib's prebuilt oleans are several GB and take a
  few minutes to download. This happens once, in `./formal setup`.
