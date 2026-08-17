# formal

## Rust

The workspace is `rust/`, in four crates:

- `formal-core` — what can be held to a fixture: the cache key, the spec file,
  the hint table, the guide. No files, no Lean, no requests.
- `formal-lean` — where Lean is, how it is confined, and how it is run.
- `formal-service` — what formal does with a proof: screen, check, remember.
- `formal-server` / `formal-cli` — the HTTP surface, and the binary named `formal`.

After every change, from `rust/`:

```sh
cargo fmt --all
cargo clippy --all-targets
cargo test
```

Edition 2024, `clippy::pedantic` denied, lint table in the workspace manifest.
`rustfmt.toml` uses nightly-only options, so formatting needs a nightly rustfmt.

`formal-lean::env::Env` is where configuration comes from. Read it from there
rather than calling `std::env::var`: setting a variable in a live process is
unsafe in Rust 2024, and every constructor already takes a `resolve(&Env)`.

`formal_core::pystr` exists because the frozen fixtures were recorded from
Python. Its idea of whitespace and of a line boundary is the specification for
anything the cache key touches — reaching for `str::lines` or
`char::is_whitespace` instead is how the keys move.

## The files that judge changes

Four things outside `rust/` decide whether a change is allowed to land. All are
data, and none of them mention an implementation.

- `tests/conformance/golden/responses.json` — the HTTP surface. 27 steps, status
  codes everywhere including the refusals, bodies where formal writes them.
  Driven by `formal-server/tests/conformance.rs`, which can also judge an
  already-running server:

  ```sh
  FORMAL_CONFORMANCE_URL=http://127.0.0.1:1337 cargo test -p formal-server --test conformance
  ```

  Re-record only deliberately, and read the diff — a line moving in that file is
  a decision, not a detail.

- `tests/fixtures/cache_keys.toml` — the exact digests. Get these wrong and every
  cached proof is silently unreachable: the answers stay correct, they just cost
  a Lean run each, forever.

- `tests/fixtures/hint_corpus.toml` — every hint pinned to its text, and every
  rule in the table reached by a sample.

- `rust/formal-core/guidance/` — the text formal serves. Its three topic bodies
  are pinned by digest inside `responses.json`, so an edit there moves a golden
  entry and has to be re-recorded on purpose.

## Hints

The advice for a failing proof lives in `rust/formal-core/guidance/hints.toml`,
not in Rust. `hints.rs` is only the matcher. When adding a rule:

- Order is the semantics — a general rule placed above a specific one swallows it.
- Add a sample to `tests/fixtures/hint_corpus.toml` that reaches it. A rule with
  no sample fails `every_rule_answers_at_least_one_sample`, which is the only
  thing standing between the table and a rule nobody can ever trigger.

## Lean

The tests that need Lean do nothing when there is none, so `cargo test` is safe
without it and much slower with it. They are the only thing that says formal
still checks proofs:

```sh
cargo test -p formal-lean --test lean          # a true theorem, a false one, a hole, a batch
cargo test -p formal-lean --test guide_lemmas  # every lemma the guide names still exists
```
