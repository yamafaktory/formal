# 🔬 formal

Automatically verifies mathematical properties of pure logic in any feature your AI coding agent writes or modifies, using Lean 4 + Mathlib as the proof backend.

Works with any LLM — Claude, GPT-4, Gemini, Llama, Mistral, or any OpenAI-compatible endpoint.

## How it works

```
Your code (any language)
  → LLM extracts pure functions
  → LLM screens each property for Lean formalizability
  → LLM translates verifiable properties into Lean 4 theorems
  → Lean 4 + Mathlib proves or rejects each theorem (with retries)
  → Results: verified / failed / unverifiable
```

Side effects (DB calls, HTTP, I/O) are excluded — only pure, deterministic logic is verified. Properties that depend on reference equality, reflection, or other runtime behaviour are classified as `unverifiable` (not a bug, not a failure).

## Setup

### 1. Configure your LLM provider

```sh
./setup.sh
```

Two backends to choose from:

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

`setup.sh` writes the right `COMPOSE_FILE` to `.env` automatically — no manual config needed. Available models are fetched from `/v1/models`; if unsupported, enter the model name manually.

### 2. Build and start

```sh
docker compose up --build
```

The first build takes several minutes — it installs Lean 4 and downloads prebuilt Mathlib oleans. Subsequent starts are instant.

```sh
./formal status
# {"status":"ok"}
```

### 3. Add this to your project's AI agent instructions

For Claude Code, add to your `CLAUDE.md`. For Cursor, Copilot, or other agents, add to the equivalent instructions file.

```markdown
## Formal Verification

A formal verifier runs at http://localhost:1337. After implementing any feature
that contains non-trivial pure logic (calculations, transformations, validations,
business rules), verify it:

```sh
~/dev/formal/formal verify /absolute/path/to/file.java
```

**When to verify:** after writing or modifying pure domain logic — pricing
calculations, volume computations, data transformations, validation functions.

**When to skip:** pure I/O code, controller wiring, configuration, tests.

Results:
- `full` — all properties proved
- `partial` / `failed` — investigate unverified properties; may indicate a logic bug
- `unverifiable` — modeling limitation (reference equality, reflection, etc.), not a bug
```

## CLI

The `formal` script is the primary interface. All commands talk to `localhost:1337`.

```sh
# Watch live logs — see generated Lean code, proof attempts, retries in real time
./formal watch

# Verify a file (language auto-detected from extension)
./formal verify path/to/Feature.java

# Verify inline code
./formal verify --code 'def f(x): return max(0, x)' --lang Python

# Full JSON response
./formal verify path/to/Feature.java --full

# Health check
./formal status
```

### Watch output

`formal watch` streams structured logs from the container:

```
[PIPELINE] Decomposing feature [Java]: SomeService.java
[PIPELINE] Pure functions: ['computePrice', 'applyDiscount']
[PIPELINE] Extracted 5 properties
[SCREEN  ] ✓ prop_1: VERIFIABLE — discount is always between 0 and 1
[SCREEN  ] ~ prop_3: UNVERIFIABLE — depends on reference equality
[VERIFY  ] prop_1 [bound] Formalizing: discount is always between 0 and 1
[LEAN    ] prop_1 theorem: import Mathlib ...
[VERIFY  ] prop_1 generating proof (attempt 1/3)...
[OK      ] prop_1 ✓ verified
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
─────────────────────────────────────────
  ✓ [bound] discount is always between 0 and 1
  ✓ [identity] zero discount returns original price
  ✓ [monotonicity] higher discount yields lower price
  ✓ [invariant] price is always positive
  ~ [invariant] bundleId reference matches stored entity
      → depends on JVM reference equality, not structural equality
─────────────────────────────────────────
```

## API reference

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

Supported languages: Python, Java, Kotlin, TypeScript, JavaScript, Go, Rust, C#, C++, Ruby, Zig, C.

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
| `full` | All verifiable properties proved |
| `partial` | ≥50% of verifiable properties proved |
| `failed` | <50% of verifiable properties proved |
| `no_pure_logic` | No pure functions found |

**Property status:**

| Status | Meaning |
|---|---|
| `verified` | Lean 4 accepted the proof |
| `failed` | Proof could not be found — may indicate a logic bug |
| `unverifiable` | Property cannot be modelled in Lean 4 (not a bug) |

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

Set in `.env` (created by `setup.sh`), overridable via environment variables:

| Variable | Description |
|---|---|
| `LLM_BACKEND` | `claude-cli` or `openai` (set by `setup.sh`) |
| `LLM_BASE_URL` | Base URL of any OpenAI-compatible endpoint |
| `LLM_API_KEY` | API key (leave empty for local models) |
| `LLM_MODEL` | Model name as accepted by the provider |
| `MAX_PROOF_RETRIES` | Retry attempts per property on Lean errors (default: `3`) |
| `MAX_PARALLEL_PROPERTIES` | Concurrent property verifications (default: `4`) |
| `LEAN_TIMEOUT` | Seconds before a Lean check times out (default: `120`) |

## Limitations

- **Pure logic only.** Side effects (DB, HTTP, I/O) are excluded by design.
- **Modeling assumptions.** Floats are modelled as rationals, strings use structural equality. Properties that require IEEE 754 precision or reference semantics are classified `unverifiable`.
- **Lean timeout.** Complex proofs may time out — increase `LEAN_TIMEOUT` if needed.
- **First build is slow.** Installing Lean 4 + Mathlib oleans takes several minutes.
- **Not a test replacement.** Formal verification proves properties hold for all inputs; it does not replace integration or end-to-end tests.
