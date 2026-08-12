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
- Error hint branches in `lean_verifier.py` — add a test case for every new branch
- JSON parsing in `feature_extractor.py` — cover normal, missing fields, and parse error
- Cache behaviour in `proof_cache.py` — key determinism, save/load, TTL

Do not test LLM output quality or Lean proof correctness — those require the
full runtime and are covered by integration use.
