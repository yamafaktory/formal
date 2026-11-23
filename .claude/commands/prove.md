---
description: Prove properties about formal's own pure functions, using formal
argument-hint: "[target, e.g. lean_text | without_comments]"
---

Point formal at its own Rust and come back with proved properties. You are not here to
change the Rust.

Target for this run: **$ARGUMENTS** — if that is empty, take the first pure function that
no spec covers yet. **One target per run.** Stop when it is done
rather than moving on; a long run costs more than two short ones and reviews worse.

Read `README.md` §"Driving formal from an agent" and `CLAUDE.md` first. The guide served
over HTTP is the authority on the workflow — this file only says what is already done,
what to aim at, and what not to break.

## What already exists

formal's own properties live in Lean specs: `spec/` holds one spec per module, named after
it, with the proofs in `proofs/<Namespace>/`. Read the spec of your module before you write
a property, and do not restate one. See `CLAUDE.md` §"Specs".

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
POST /session {"spec": "<absolute path to spec/<Module>.lean>"}
GET  /guide/formalize            Lean 4 conventions for stating a property
GET  /guide/tactics              read before writing a proof, not after it fails
POST /session/{id}/check         {"proofs": {"<id>": "<lean>"}}
```

`spec` must be absolute — the server's working directory is not yours.
`/guide/{topic}` takes exactly `extract`, `formalize`, `tactics`.

## Where to aim

Pure, total, no I/O. Every module below has a spec, so a new property goes into it:

- `rust/formal-core/src/pystr.rs` — `spec/Pystr.lean`
- `rust/formal-core/src/proof_cache.rs` — `spec/ProofCache.lean`
- `rust/formal-core/src/hints.rs` — `spec/Hints.lean`
- `rust/formal-core/src/specs.rs` — `spec/Specs.lean`
- `rust/formal-lean/src/run.rs` — `spec/Run.lean`
- `rust/formal-lean/src/verifier.rs` — `spec/Verifier.lean`

A pure function in a module without a spec gets a new spec, `spec/<Module>.lean`.

Not targets: `run_command` and anything else touching processes, threads, clocks or the
filesystem; the sandbox; the server wiring. Not pure, not provable, not the point.

## Rules

- **Never edit the Rust to make a proof go through.** If a property will not close, the
  property is wrong or an assumption is missing. If you believe the *code* is wrong, say
  so and stop — do not fix it here.
- **One model per function.** Model a function once in its spec, and state every
  property against that model. A function with plain inputs gets a `code:` line and
  `<name>.inputs`, and a row in the `answer` table of `formal-lean/tests/spec.rs`.
- Write each property as `def <function>_<claim> : Prop` in the spec. Save its proof as
  `proofs/<Namespace>/<function>_<claim>.lean`, declaring
  `theorem <Namespace>.<function>_<claim>.holds`. `formal-service/tests/spec_sessions.rs`
  checks every one. A spec uses core Lean only.
- **Do not touch the four judging files**: `tests/conformance/golden/responses.json`,
  `tests/fixtures/cache_keys.toml`, `tests/fixtures/hint_corpus.toml`,
  `rust/formal-core/guidance/`.
- **Each spec proof is its own Lean run,** because spec proofs are never batched. Read
  `/guide/tactics` before the first attempt — most first-attempt failures are already on
  that list.
- **Turn count is the cost** (~$0.11/turn here; context re-reads dominate, not payload).
  Read a file once. Do not re-extract properties you have already written.
- Before finishing, from `rust/`: `cargo +stable test --workspace --locked`, and the two
  spec tests in `CLAUDE.md` §"Lean". Nothing you wrote should have touched the Rust, and
  this is how you find out that it did.
- **Do not commit.** Stage the spec and the `.lean` proofs, and hand over a commit
  message — the human commits.

## Report back

- Each property: id, function, what it claims, and its assumptions in plain words.
- Anything that would not prove, and whether the fault is in the property, the assumption,
  or the code.
- Turns, wall time, and how many proofs came back cached or were closed by the
  auto-tactic chain before reaching you. Nobody has that number for these targets yet.
