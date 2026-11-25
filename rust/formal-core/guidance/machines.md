A spec can describe a state machine: `def init : <State>` and `def step : <State> → <Action> → <State>` in its namespace, with at least one invariant `def <name> : <State> → Prop` or `def <name> (s : <State>) : Prop`. formal then defines `run`, the fold of `step` over a list of actions from `init`, so the spec must not define `run`.

formal registers each invariant as `<Namespace>.<name>.always`, which states `∀ actions, <name> (run actions)`. Its proof declares `theorem <Namespace>.<name>.always.holds : <Namespace>.<name>.always`. The search derives the generators for the spec's types, so a broken invariant comes back with the trace that breaks it.

When the actions of a machine are known, formal also explores every state up to a depth, 10 unless the spec defines `def depth : Nat`. The actions are the constructors of the action type when none takes an argument, else `<Action>.samples`. A violation comes back under refuted with its shortest trace, and an invariant that held comes back under bounded.

The check stops after 100000 states. bounded then gives the last depth it explored in full, which can be less than the depth asked for.

A `code:` line on `step` replays the machine against the code. The session lists `<Namespace>.run` under compare, with one trace of actions per state the bounded walk reached. Replay each trace on the code and send the last state.

Actions and states cross in Lean's derived JSON. A structure is an object of its fields, and text a string. A constructor with no argument is its name. One with named arguments is `{"add": {"n": 1}}`, one with one anonymous argument `{"one": 1}`, and one with several `{"two": [2, false]}`. `none` is `null`, and a trace of `Char` actions is a string.

formal also tests whether each invariant the checks did not refute is inductive: a state where it holds and an action whose next state breaks it come back under not_inductive, so its proof needs a stronger invariant. When such invariants are kept by every step together, inductive_together names them: prove them in one induction. `<State>.samples` steers the states.

`import Formal.Temporal` gives a spec `Temporal.always`, `eventually` and `leadsTo` over `init` and `step`, and `Temporal.fair a`. Fairness holds only where a property states it, and some run must satisfy it: `fair_constant` or `fair_cycle` gives one. The rules are `always_of_inductive`, `leadsTo_of_measure`, `leadsTo_of_fair_step`, `leadsTo_trans`, `leadsTo_or` and `eventually_of_leadsTo`.

formal checks a liveness property written as `Temporal.leadsTo init step A p q` or `Temporal.eventually init step A q`, with `A` made of `Temporal.fair` or `fun _ => True`, on the states the walk reached. A loop that takes every fair action and never reaches `q` comes back under refuted, as the actions to the loop, then the loop. It is bounded only when the walk reached every state.
