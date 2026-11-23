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

Five things decide whether a change is allowed to land. All are data. Only
`formal.properties.json` quotes the implementation.

- `tests/conformance/golden/responses.json` — the HTTP surface. 35 steps, status
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

- `formal.properties.json` — formal's own properties. Two tests in
  `formal-core/tests/specs.rs` fail when a property is stale, or when its
  `function_code` does not hold the function it names. They do not check proofs. A
  change to a function updates the property's `function_code`, and its proof in
  `proofs/` has to pass formal again, by hand.

## Hints

The advice for a failing proof lives in `rust/formal-core/guidance/hints.toml`,
not in Rust. `hints.rs` is only the matcher. When adding a rule:

- Order is the semantics — a general rule placed above a specific one swallows it.
- Add a sample to `tests/fixtures/hint_corpus.toml` that reaches it. A rule with
  no sample fails `every_rule_answers_at_least_one_sample`, which is the only
  thing standing between the table and a rule nobody can ever trigger.

Lean words a tactic failure differently from tactic to tactic and from version to
version. `[handler.tactic_failed] patterns` lists the wordings it recognises, and
the first match names the tactic. A wording missing from that list sends the
failure to the generic fallback without any test failing. When Lean rewords a
failure, add the new wording there, and record the corpus sample from a real Lean
run, never from memory.

## Specs

A Lean spec says what code must do. `spec/Pystr.lean` is the one for
`formal_core::pystr`. Each `def <name> : Prop :=` in it is a property, and its proof
is `proofs/Pystr/<name>.lean`, which declares `theorem Pystr.<name>.holds`.

formal checks a spec itself: `POST /session` with `{"spec": path}`.
`formal-core/src/lean_spec.rs` reads the spec and composes each proof after it. A
header line `import Spec.<Name>` reads `<Name>.lean` from the directory of the spec the
session opens on, for nested imports too.
`LeanSpec::source` is what Lean reads: the imported specs in dependency order, then
the spec, under one header of their real imports. Every cache key digests the source. The
composed file ends with `#formal_holds "<id>"`, which finds `<id>.holds` by name and
requires its type to be the property. Like `#formal_audit`, it is defined in the
`FormalAudit` module (`formal-lean/lean/FormalAudit.lean`), which every check imports
before the proof, so no notation or variable in the proof can change what it does.
`Checker::check_against` composes at the Lean boundary, so the screen, the recovery
chain and the cache all see the proof alone. Each proof of a spec costs its own Lean
run: one file cannot hold the spec once per proof, so spec proofs are never batched.

A spec function that names its code in a `code:` line of its doc comment is compared
with that code. `def <name>.inputs` lists the inputs, and a spec without it is refused.
`LeanSpec::evaluation` builds one file that prints the inputs and the spec's answers.
formal runs it when the session opens and caches the answers per spec text. The caller
runs its code and sends the answers to `POST /session/{id}/compare`. The evaluation
prints JSON through `Lean.ToJson`, with a `List Char` as a string.

`LeanSpec::search` builds one file that searches each property for a counterexample
with Plausible, one property per line, and reads Lean's answer on that line. The file
defines a `Testable` instance for `∀ x ∈ l`, and draws half of the values of each type
the spec lists `<Type>.samples` for from that list. formal runs it when the session
opens and caches each answer Lean gave. A refuted property stays work.

`formal-service/tests/spec_sessions.rs` checks every proof of `spec/Pystr.lean` through
a session, and holds the check to proofs that try to cheat. `formal-lean/tests/spec.rs`
runs that evaluation on `spec/Pystr.lean` and compares the Rust with each answer. The
spec uses core Lean only.

## Lean

The tests that need Lean do nothing when there is none, so `cargo test` is safe
without it and much slower with it. They are the only thing that says formal
still checks proofs:

```sh
cargo test -p formal-lean --test lean          # a true theorem, a false one, a hole, a batch
cargo test -p formal-lean --test audit         # the false theorems Lean accepts and formal must not
cargo test -p formal-lean --test warm          # a warm Lean gives the verdict a cold one gives
cargo test -p formal-lean --test confinement   # bubblewrap confines what it claims to
cargo test -p formal-lean --test guide_lemmas  # every lemma the guide names still exists
cargo test -p formal-lean --test spec          # the Rust answers what the spec answers
cargo test -p formal-service --test spec_sessions  # every proof of the spec holds, and no cheat does
```

CI runs all seven in the `lean` job, sandboxed, and fails before them if Lean or
the REPL is missing, so none of them can pass by skipping.

## Releases

Every pull request is a release. It bumps `version` in `rust/Cargo.toml` (and
so `Cargo.lock`) as one of its own commits, following semver:

- major — something that worked stops working: a route, a body field or a
  status code in `responses.json`, a CLI command or flag, or a configuration
  variable is removed or changes meaning.
- minor — something new: a route, a command, a flag, a variable, a hint rule.
- patch — everything else: fixes, docs, CI, refactors.

Two pull requests open at once both bump from the same base; whichever merges
second rebases and bumps again. Once a pull request merges, run
`scripts/release.sh <version>` on `main` to tag it.

The script runs from a clean `main` that matches `origin/main`, refuses a
version `rust/Cargo.toml` does not already carry, then tags `v<version>` and
pushes the tag. It asks before pushing; `--yes` does not, which a shell with no
input needs. The tag runs `release.yml`, which builds the binaries `install.sh`
downloads and refuses a tag that does not match `rust/Cargo.toml`.

## Commits and pull requests

No `Co-Authored-By` trailer on commits, and no "Generated with Claude Code" line
in pull request descriptions.
