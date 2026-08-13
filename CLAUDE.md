# formal

## Python

The package lives in `src/formal/`. After every Python file change, run:

```sh
uv run ruff check .
uv run ruff format .
```

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

## Hints

The advice returned for a failing proof lives in `src/formal/guidance/hints.toml`,
not in Python. `hints.py` is only the matcher. When adding a rule:

- Order is the semantics — a general rule placed above a specific one swallows it.
- Add a sample to `tests/fixtures/hint_corpus.json` that reaches it. A rule with
  no sample fails `TestNoRuleIsUnreachable`, which is the only thing standing
  between the table and a rule nobody can ever trigger.
