---
description: Prove properties about formal's own pure functions, using formal
argument-hint: "[target, e.g. pystr | verifier | parse_output | hints]"
---

Point formal at its own Rust and come back with proved properties. You are not here to
change the Rust.

Target for this run: **$ARGUMENTS** — if that is empty, take the first entry under
"Where to aim" that has no properties yet. **One target per run.** Stop when it is done
rather than moving on; a long run costs more than two short ones and reviews worse.

Read `README.md` §"Driving formal from an agent" and `CLAUDE.md` first. The guide served
over HTTP is the authority on the workflow — this file only says what is already done,
what to aim at, and what not to break.

## What already exists

`formal.properties.json` holds three properties, all against
`rust/formal-core/src/proof_cache.rs`, with their Lean in `proofs/`:
`normalise_code/length_non_increasing`, `framed/shifting_a_boundary_changes_the_payload`,
`normalise_formal/word_operators_respect_boundaries`. Two of the three were written after
formal found a real cache-key collision. Do not restate them.

Everything else in the workspace is unproved.

## Running it

The binary is **not on `PATH`**, so the README's bare `formal …` will not work. From
`rust/`:

```sh
cargo run --bin formal -- status                # expect: mathlib oleans built, sandbox bubblewrap
cargo run --bin formal -- serve --background    # returns once /health answers; no-op if already up
cargo run --bin formal -- stop
```

It serves on `http://127.0.0.1:1337`.

## The loop

```
GET  /guide                      the workflow and the spec-file schema
GET  /guide/extract              how to find pure functions and properties
POST /session {"spec_file": "<absolute path to formal.properties.json>"}
GET  /guide/formalize            Lean 4 conventions for stating a property
GET  /guide/tactics              read before writing a proof, not after it fails
POST /session/{id}/check         {"proofs": {"<id>": "<lean>"}}
```

`spec_file` must be absolute — the server's working directory is not yours.
`/guide/{topic}` takes exactly `extract`, `formalize`, `tactics`.

## Where to aim

Pure, total, no I/O — in order of value:

1. **`rust/formal-core/src/pystr.rs`** — `splitlines`, `strip`, `rstrip`, `is_space`.
   `CLAUDE.md` calls this the *specification* for anything the cache key touches: Python's
   idea of a line boundary, not Rust's. Highest value in the workspace, no properties yet.
2. **`rust/formal-lean/src/verifier.rs`** — `split_imports`, `build_batch`, `rebase`.
   Batching is where a wrong answer gets attributed to the wrong proof: `rebase` maps a
   Lean error's line back into its entry, and "a rebased line lands inside the entry it is
   attributed to" is the claim a test samples and a proof settles.
3. **`rust/formal-lean/src/run.rs::parse_output`** — pure and load-bearing: a `sorry` is a
   *warning* to Lean and a failure here. "Success implies no promoted sorry", "errors
   precede promoted sorries".
4. **`rust/formal-core/src/hints.rs`** — order is the semantics; a general rule above a
   specific one swallows it. "The first matching rule wins."

Not targets: `run_command` and anything else touching processes, threads, clocks or the
filesystem; the sandbox; the server wiring. Not pure, not provable, not the point.

## Rules

- **Never edit the Rust to make a proof go through.** If a property will not close, the
  property is wrong or an assumption is missing. If you believe the *code* is wrong, say
  so and stop — do not fix it here.
- **`function_code` must be the current source, copied exactly.** If it drifts the
  property comes back `stale` and is never proved. Copy from the working tree.
- Append to `formal.properties.json` (`version: 1` stays). Save each proof as
  `proofs/<function>_<short>.lean`, matching the three already there. Nothing reads
  `proofs/` — it is the committed record.
- **Do not touch the four judging files**: `tests/conformance/golden/responses.json`,
  `tests/fixtures/cache_keys.toml`, `tests/fixtures/hint_corpus.toml`,
  `rust/formal-core/guidance/`.
- **Batch.** Every proof in one `check` request pays a single `import Mathlib` (~3.2s);
  one request per proof pays it each time. Read `/guide/tactics` before the first attempt
  — most first-attempt failures are already on that list.
- **Turn count is the cost** (~$0.11/turn here; context re-reads dominate, not payload).
  Read a file once. Do not re-extract properties you have already written.
- Before finishing, from `rust/`: `cargo +stable test --workspace --locked`. Nothing you
  wrote should have touched the Rust, and this is how you find out that it did.
- **Do not commit.** Stage the spec file and the `.lean` proofs, and hand over a commit
  message — the human commits.

## Report back

- Each property: id, function, what it claims, and its assumptions in plain words.
- Anything that would not prove, and whether the fault is in the property, the assumption,
  or the code.
- Turns, wall time, and how many proofs came back cached or were closed by the
  auto-tactic chain before reaching you. Nobody has that number for these targets yet.
