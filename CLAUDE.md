# formal

## Python

The package lives in `src/formal/`. After every Python file change, run:

```sh
uv run ruff check .
uv run ruff format .
```

## Rust

The port lives in `rust/`, a workspace beside the Python it replaces. Both run at
every commit: Python keeps serving until the Rust binary answers the conformance
suite, and the two are compared through the golden files rather than by reading
each other. After every Rust change, run:

```sh
cargo fmt --all
cargo clippy --all-targets
cargo test
```

Edition 2024, `clippy::pedantic` denied, the lint table in the workspace manifest.
`formal-core` is the part that can be held to a fixture — no files, no Lean, no
requests.

`pystr` exists because the golden digests were recorded from Python, so Python's
idea of whitespace and of a line boundary is the specification here. Reaching for
`str::lines` or `char::is_whitespace` instead is how the keys move.

## Shell

After every shell file change, run:

```sh
shfmt -w formal
shellcheck formal
```

## Tests

Tests live in `tests/`. Run them with:

```sh
uv run pytest --tb=short
```

When adding new code, add tests for anything that is pure or can be tested
with a mocked LLM (`unittest.mock.patch`). Good candidates:

- Pure logic (string transformations, hash functions, data parsing)
- Cache behaviour in `proof_cache.py` — key determinism, save/load, TTL
- Spec loading and staleness in `specs.py`

Do not test Lean proof correctness — that requires the full runtime and is
covered by integration use.

## Conformance

`tests/conformance/` states the HTTP surface without reference to Python, and
`tests/conformance/golden/responses.json` says what each request must answer.
It runs as part of `pytest`, and against any server:

```sh
PROOF_CACHE_DIR=$(mktemp -d) uv run --group dev python -m uvicorn formal.api:app --port 8000
uv run --group dev python -m tests.conformance.run --base-url http://127.0.0.1:8000
```

Add `--update` to re-record after a deliberate change, and read the diff — that
file is the contract, so a line moving in it is a decision, not a detail. The
server under test needs an empty `PROOF_CACHE_DIR`, or properties the suite
expects to be unproved come back cached.

Two other golden files exist for the same reason: `tests/fixtures/cache_keys.json`
(the exact digests — get these wrong and every cached proof is silently
unreachable) and `tests/fixtures/hint_corpus.json`.

## Hints

The advice returned for a failing proof lives in `src/formal/guidance/hints.toml`,
not in Python. `hints.py` is only the matcher. When adding a rule:

- Order is the semantics — a general rule placed above a specific one swallows it.
- Add a sample to `tests/fixtures/hint_corpus.json` that reaches it. A rule with
  no sample fails `TestNoRuleIsUnreachable`, which is the only thing standing
  between the table and a rule nobody can ever trigger.
