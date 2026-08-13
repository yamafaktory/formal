Separate the pure logic in the file from everything else.

For each function, decide whether it is pure: the same inputs always produce the same
result, with no I/O, no database, no network and no global state. This step produces no
document — you are deciding which functions are worth stating properties about, and
noting in a sentence what the file does overall. Carry that into the next step.

Rules:
- Pure functions: no DB, no I/O, no HTTP, no global state, same input always gives same output
- A function is STILL PURE if its arguments are objects, structs, interfaces or closures and it only
  READS from them — calling an accessor, projecting a field, applying a function it was handed.
  Reading from an argument is not a side effect.
- Non-exported or private helpers that compute strings, numbers, collections or booleans from their
  arguments are almost always pure — classify them as pure unless they explicitly do I/O or mutate
  state reachable from outside.
- If a function mixes pure and impure, extract just the pure computation as a new helper
- If nothing in the file is pure, there is nothing to prove here — say so and stop
- When you record a function's source in the spec file, copy it verbatim from the file
