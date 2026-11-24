# Measuring what formal adds

This benchmark measures whether formal reduces wrong "verified" claims, as #24
proposes. An agent checks the same functions two ways:

- **`lean`:** the agent has Lean 4 and Mathlib.
- **`formal`:** the agent has Lean 4 and Mathlib, and formal.

The agent reads one function and one property, and answers `verified`,
`refuted` or `unknown`. A hidden property test then runs the real code on many
generated inputs and decides whether the property holds. The agent never sees
that test.

A claim is a **wrong verified** when the agent answers `verified` and the hidden
test breaks the property. That is the number formal must bring down.

## The corpus

`tasks.toml` lists 20 functions from well-known open-source projects: six in
Python, seven in Rust and seven in TypeScript. `vendor/` holds their code, pinned
to one commit, and `vendor/README.md` says where each file comes from.

Each task states its property in plain words, from the function's own
documentation. In 10 tasks, the code breaks its property in one place:
`hidden/seeds.toml` plants that bug before the agent sees the code.

`hidden/` holds one property test per task: Hypothesis for Python, proptest for
Rust and fast-check for TypeScript.

## Running it

The script needs `uv`, `cargo`, `node` and `npm`, `bwrap`, the `claude` CLI,
and Lean with Mathlib in `lean_project/` (`formal setup` installs it). Install the
TypeScript test library once:

```sh
npm ci --prefix bench/hidden/typescript
```

Check that each hidden test passes on the original code, and fails on the
seeded code of each seeded task:

```sh
uv run bench/bench.py check
```

Run the agent. Each task runs three times in each arm:

```sh
uv run bench/bench.py run
uv run bench/bench.py report
```

`run` appends one record per run to `bench/results/records.jsonl`, and `report`
prints one row per arm. `report` also names the tasks where the arms disagree.
Run those tasks again, and the new runs count with the old ones:

```sh
uv run bench/bench.py run --only rs-gcd ts-chunk
```

`run` refuses to start when a hidden test disagrees with its seed.

## How a run works

- **The agent** is Claude Code in headless mode, with one model for both arms
  (`--model`, `claude-opus-5-5` by default). It runs with `--safe-mode`, so no
  `CLAUDE.md`, skill, plugin or MCP server of yours reaches it. `--effort` sets
  its effort. Without it, Claude Code uses its default.
- **The agent's sandbox.** Each run starts the agent under bubblewrap, in a
  fresh temporary folder, with an empty environment. The agent sees the system
  read only, an empty home with your Claude login, the Lean and Rust toolchains,
  and its own folder. That folder holds the task's code, seeded when the task
  has a seed, and a Lean project that shares Mathlib read only. The repository,
  the seeds, the hidden tests and the other runs stay out of sight.
- **formal's sandbox.** The `formal` arm starts its own formal server under
  bubblewrap too. It sees the agent's code and Lean project read only, and its
  own home, proof cache and Lean project. So formal cannot read what the agent
  cannot read, the agent cannot touch formal's cache, and no run reuses a proof
  from another run. The prompt tells the agent where formal runs. The `lean` arm
  has no formal.
- **The limit** is 20 minutes. A run that reaches it counts as no claim, and its
  whole sandbox stops. Ctrl-C stops the runs in progress and cancels the rest.
- **The record** holds the verdict, the evidence, its grade, the tokens, the
  cost, the wall time, the effort, the Claude Code and formal versions, the
  commit, and the models that answered. A run that fails on the agent's side,
  such as an API error, is graded `error` and stays out of the means.
- **The kept files.** Each run's folder, without its home and Mathlib, stays in
  `bench/results/runs/<task>/<arm>/<run>/`, with Claude's event stream and
  stderr, so a person can audit a claim.

The sandbox has limits:

- The agent keeps network access, because Claude Code needs it. It can download
  the original code of a well-known project, and it may know that code already.
- With `--jobs` above 1, a `lean` run can reach a `formal` run's server by
  guessing its port. Keep `--jobs 1` for strict arms.
- The agent runs with `--dangerously-skip-permissions` inside the sandbox. The
  sandbox writes only to its run folder and your Claude login, but it shares the
  network with the machine.

## The script's own tests

```sh
uv run --with pytest pytest bench/test_bench.py
```
