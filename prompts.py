CODE_GENERATION_SYSTEM = """You are a Python expert. Output ONLY a clean Python function.
Include a docstring. No explanations outside the code block."""

CODE_GENERATION_USER = """Write a Python function for: {task}

Output format:
```python
def function_name(...) -> ...:
    \"\"\"...\"\"\"
    ...
```"""


SPEC_EXTRACTION_SYSTEM = """You extract formal behavioral specifications from Python code.
Be precise and mathematical. No code blocks."""

SPEC_EXTRACTION_USER = """Extract a formal specification from this Python function.

Include:
- Function signature and types
- Preconditions (what must hold on inputs)
- Postconditions (what the output guarantees)
- Key invariants or properties (e.g. monotonicity, termination argument)

Code:
{code}"""


AUTOFORMALIZE_SYSTEM = """You are a Lean 4 expert. Output ONLY valid Lean 4 code in a lean4 code block.
Use Lean 4 syntax — not Lean 3. All types must be from Lean 4 / Mathlib."""

AUTOFORMALIZE_USER = """Translate this specification into a Lean 4 theorem statement.

Rules:
- Start with `import Mathlib` or specific Mathlib imports
- Use Lean 4 types: Nat, Int, List, Array, Bool, etc.
- Write 1–3 theorem/lemma statements that capture the core properties
- End each theorem with `:= by sorry` (proof placeholder)
- Do NOT include a proof yet

Specification:
{spec}

Output ONLY a lean4 code block."""


AUTOFORMALIZE_RETRY_USER = """Your previous Lean 4 output had this error:

{error}

Fix it and output the corrected Lean 4 theorem statement.
Remember: use Lean 4 syntax, end with `:= by sorry`.

Previous attempt:
{previous}

Output ONLY a lean4 code block."""


PROOF_GENERATION_SYSTEM = """You are a Lean 4 tactic proof expert.
Output ONLY valid Lean 4 code in a lean4 code block."""

PROOF_GENERATION_USER = """Replace every `sorry` in this Lean 4 theorem with a real proof.

Available tactics: simp, omega, induction, rfl, exact, apply, intro, cases,
decide, norm_num, ring, linarith, aesop, constructor, use, have, calc,
unfold, gcongr, positivity, exact?, apply?.

Critical rules:
- `simp` may fully close a goal on its own — NEVER add more tactics after it
  unless you are certain there is a remaining goal. Prefer:
    simp [f]
  over:
    simp [f]
    exact something  ← will crash with "no goals" if simp already closed it
- After `simp` leaves a residual goal, use `linarith` or `omega`, not `constructor`
- For max/min bound proofs use: `exact le_max_left _ _`, `exact le_max_right _ _`,
  `exact min_le_left _ _`, `exact min_le_right _ _`
- For goals that are already a hypothesis, use `exact h` or `assumption`, not `constructor`
- Use `unfold f` instead of `simp [f]` when you want to expand without risking
  the goal being closed prematurely
- Use `omega` for linear arithmetic on Nat/Int
- Use `linarith` for linear arithmetic on ℚ/ℝ
- Use `decide` for decidable propositions on small finite types
- Use `induction n` for natural number induction
- For Bool goals: `x = true` and `¬(x = false)` are NOT automatically interchangeable.
  Use `decide`, `cases x <;> simp`, or `simp [Bool.eq_true_iff_ne_false]` to normalise.
- To unfold a local definition across both goal and hypotheses: `unfold f at *` or `simp only [f] at *`.
  If `simp [f]` makes no progress on a hypothesis `h`, try `unfold f at h` or `delta f at h`.

Mathlib API reference — use EXACTLY these names, do not guess alternatives:

List:
  List.length_singleton    : [a].length = 1
  List.length_cons         : (a :: l).length = l.length + 1
  List.length_nil          : [].length = 0
  List.mem_singleton       : a ∈ [b] ↔ a = b
  List.mem_cons            : a ∈ b :: l ↔ a = b ∨ a ∈ l
  List.mem_cons_self       : a ∈ a :: l   (use as `exact List.mem_cons_self _ _` or just `simp`)
  List.mem_nil_iff         : a ∈ ([] : List α) ↔ False
  List.mem_append          : a ∈ l ++ m ↔ a ∈ l ∨ a ∈ m
  List.head?_cons          : List.head? (a :: l) = some a
  List.head?_nil           : List.head? ([] : List α) = none
  List.getLast?_cons_nil   : List.getLast? [a] = some a
  List.nodup_singleton     : List.Nodup [a]
  List.singleton_append    : [a] ++ l = a :: l
  List.length_pos_of_ne_nil: l ≠ [] → 0 < l.length  (or use: List.length_pos)
  List.ne_nil_of_length_pos: 0 < l.length → l ≠ []

Option:
  Option.some_injective    : some a = some b → a = b
  Option.get_some          : Option.get (some a) h = a
  Option.isSome_iff_exists : o.isSome = true ↔ ∃ a, o = some a

Nat / Int arithmetic:
  Nat.succ_ne_zero         : Nat.succ n ≠ 0
  Nat.lt_irrefl            : ¬ n < n
  Nat.le_of_lt_succ        : n < m + 1 → n ≤ m

Key tactic patterns:
- Destructure a length-1 list into a concrete singleton (do NOT use List.length_eq_one):
    cases l with
    | nil => simp at h
    | cons a t =>
      cases t with
      | nil => -- l is now [a]; continue proof
        ...
      | cons b t => simp at h; omega
- Prove membership after reducing to [a]:
    simp  -- preferred: handles membership goals automatically
    -- alternative: exact List.mem_cons_self _ _  (use _ wildcards, NOT explicit a [])
- For `f [a] ∈ [a]` where f returns the only element: after casing to [a],
  unfold f, then `simp [List.head?_cons, List.mem_singleton]`

Theorem to prove:
{theorem}

Output ONLY a lean4 code block with the proof filled in."""


# ── Feature-level prompts ─────────────────────────────────────────────────────

DECOMPOSE_SYSTEM = """You are an expert at separating pure logic from side-effectful code.
Respond ONLY with valid JSON. No markdown, no explanation."""

DECOMPOSE_USER = """Analyze this {language} feature code and decompose it.

Return a JSON object with:
{{
  "pure_functions": [
    {{
      "name": "function name",
      "code": "the extracted pure function as a string",
      "description": "what it does in one sentence"
    }}
  ],
  "impure_parts": ["description of side effects: DB calls, HTTP, I/O, etc."],
  "feature_summary": "one sentence describing the overall feature"
}}

Rules:
- Pure functions: no DB, no I/O, no HTTP, no global state, same input always gives same output
- If a function mixes pure and impure, extract just the pure computation as a new helper
- If nothing is pure, return empty pure_functions array
- Preserve the original {language} syntax when extracting pure function code

Feature code:
{code}"""


PROPERTY_EXTRACTION_SYSTEM = """You are an expert at identifying formal properties of code.
Respond ONLY with valid JSON. No markdown, no explanation."""

PROPERTY_EXTRACTION_USER = """Given these pure functions extracted from a feature, identify verifiable properties.

Pure functions:
{pure_functions}

Feature summary: {feature_summary}

Return a JSON object:
{{
  "properties": [
    {{
      "id": "prop_1",
      "description": "human-readable property description",
      "function": "which pure function this applies to",
      "kind": "one of: bound, identity, monotonicity, commutativity, idempotency, invariant",
      "formal": "mathematical statement, e.g. forall x, f(x) <= x"
    }}
  ]
}}

Focus on properties that are:
- Mathematically precise (not vague)
- Actually checkable by Lean 4
- Meaningful for correctness (not trivial)

Aim for 2-5 properties per pure function. Max 10 total."""


# ── Property screening ────────────────────────────────────────────────────────

PROPERTY_SCREENING_SYSTEM = """You are an expert in formal verification and Lean 4.
Respond ONLY with valid JSON. No markdown, no explanation."""

PROPERTY_SCREENING_USER = """Assess whether each property can be formally verified in Lean 4.

A property is VERIFIABLE if:
- It can be expressed purely in terms of mathematical structures
  (numbers, lists, sets, booleans, strings with structural equality)
- Every type involved can be mapped to a concrete Lean 4 type:
    equality / comparison  →  = or ≤ on the relevant type
    membership             →  ∈ Finset / ∈ List
    optional / nullable    →  Option T
    string equality        →  = on String (which has DecidableEq)
    ordered collection     →  List T or Finset T
    map / dictionary       →  Finset (K × V) or a function K → Option V
- The proof does not require axioms about runtime behaviour
  (memory layout, JVM internals, hash codes, reference identity, etc.)

Modeling assumptions applied during verification:
- Floating-point types (float, double, Float, f64…) are modeled as Rat (rationals).
  This means NaN, Inf, and IEEE 754 rounding DO NOT EXIST in the model.
  Any property that would hold over rationals is therefore verifiable.
- String equality is structural (= on String), not reference equality.
- Collections are modeled as Finset or List with standard membership.

A property is UNVERIFIABLE only if it fundamentally depends on something
outside these models:
- Reference/pointer identity (not value equality)
- Runtime type information or reflection
- Hash codes or memory addresses
- External state, I/O, or time
- Language-specific runtime behaviour with no mathematical counterpart

When in doubt, mark as VERIFIABLE — ordering, bounds, identity, idempotency,
and monotonicity properties are almost always verifiable under these models.

Source language: {language}

Properties to assess:
{properties}

Return a JSON object:
{{
  "assessments": [
    {{
      "id": "prop_1",
      "verifiable": true,
      "lean_type_mapping": "brief note on how each type maps to Lean 4",
      "reason": "one sentence — why it is or is not verifiable"
    }}
  ]
}}"""


# ── Property formalization ────────────────────────────────────────────────────

PROPERTY_FORMALIZE_USER = """Translate this property into a Lean 4 theorem.

Source language: {language}
Function code:
{function_code}

Property:
- Description: {description}
- Formal statement: {formal}
- Kind: {kind}

Modeling rules (apply to any source language):
- Translate SEMANTICS, not syntax. Re-implement the logic in Lean 4 from scratch.
- NEVER leave a type opaque. Every value must have a concrete Lean 4 type:
    numbers          →  Nat, Int, or Rat (never an abstract "Number")
    equality checks  →  = (Lean's structural equality — never model .equals() as a function)
    strings          →  String (has DecidableEq; use = for any string comparison)
    lists / arrays   →  List T
    sets             →  Finset T (use ∈ for membership, ⊆ for subset)
    maps             →  Finset (K × V) or K → Option V
    optional / null  →  Option T
    booleans         →  Bool or decidable Prop
- If membership monotonicity is involved (x ∈ s → x ∈ s') model s' as a Finset
  superset and use Finset.mem_of_mem_of_subset or set inclusion directly.
- For functions that THROW on invalid input (guards, precondition checks):
    model the function as returning `Option T` (none = threw) or add a
    precondition hypothesis (h : l.length = 1) and prove the postcondition.
    Do NOT model exceptions as ⊥ or use Classical.choice.
- Import Mathlib at the top.
- Re-implement the function in Lean 4, then state the theorem.
- End with `:= by sorry`.
- Keep it to one self-contained Lean 4 file.

Mathlib API — use EXACTLY these names when dealing with List/Option:
  List.length_singleton    : [a].length = 1
  List.mem_singleton       : a ∈ [b] ↔ a = b
  List.mem_cons            : a ∈ b :: l ↔ a = b ∨ a ∈ l
  List.mem_cons_self       : a ∈ a :: l   (use as `exact List.mem_cons_self _ _` or just `simp`)
  List.head?_cons          : List.head? (a :: l) = some a
  List.head?_nil           : List.head? ([] : List α) = none
  List.length_pos_of_ne_nil: l ≠ [] → 0 < l.length
  Option.some_injective    : some a = some b → a = b

For "result is member of original list" proofs on length-1 guarded functions:
  Add hypothesis `(h : l.length = 1)`, then case on the list:
    cases l with
    | nil => simp at h
    | cons a t =>
      cases t with
      | nil => simp  -- or: exact List.mem_cons_self _ _
      | cons b t => simp at h; omega

Output ONLY a lean4 code block."""


PROPERTY_FORMALIZE_AND_PROVE_USER = """Formalize this property as a Lean 4 theorem AND provide a complete proof.
No sorry.

Source language: {language}
Function code:
{function_code}

Property:
- Description: {description}
- Formal statement: {formal}
- Kind: {kind}

Modeling rules:
- Translate SEMANTICS, not syntax. Re-implement the logic in Lean 4 from scratch.
- NEVER leave a type opaque. Every value must have a concrete Lean 4 type:
    numbers          →  Nat, Int, or Rat
    equality checks  →  = (Lean's structural equality)
    strings          →  String (use = for comparisons)
    lists / arrays   →  List T
    sets             →  Finset T
    maps             →  Finset (K × V) or K → Option V
    optional / null  →  Option T
    booleans         →  Bool or decidable Prop
- Import Mathlib at the top. Re-implement the function, then state and prove the theorem.
- For functions that throw on invalid input: model as Option T or add a precondition hypothesis.

Proof tactics:
- `rfl` for definitional equality
- `omega` for linear arithmetic on Nat/Int
- `norm_num` for numeric computations
- `simp [f]` to unfold and simplify — but NEVER add tactics after simp if it closes the goal
- `linarith` for linear arithmetic on ℚ/ℝ
- `decide` for decidable propositions on small finite types
- `aesop` as a last resort for structural goals

Mathlib API (use EXACTLY these names):
  List.length_singleton    : [a].length = 1
  List.mem_singleton       : a ∈ [b] ↔ a = b
  List.mem_cons            : a ∈ b :: l ↔ a = b ∨ a ∈ l
  List.mem_cons_self       : a ∈ a :: l
  List.head?_cons          : List.head? (a :: l) = some a
  List.head?_nil           : List.head? ([] : List α) = none
  List.length_pos_of_ne_nil: l ≠ [] → 0 < l.length
  Option.some_injective    : some a = some b → a = b

Output ONLY a lean4 code block with the complete theorem and proof."""


PROPERTY_RETRY_USER = """The Lean proof failed with this error:

{error}
Line: {line}, Col: {col}
Hint: {hint}

Fix the proof for this property:
- Description: {description}

Current code:
{current}

Output ONLY a corrected lean4 code block."""


PROOF_RETRY_USER = """The Lean REPL rejected your proof with this error:

{error}

Fix the proof. The error is at line {line}, column {col}.

Hint: {hint}

If the error is `unknown identifier` or `unknown constant`, do not guess lemma names.
Instead prove the goal using `simp`, `omega`, `decide`, `rfl`, or by unfolding the
definition and casing on the structure — tactics that do not rely on specific lemma names.

Current code:
{current}

Output ONLY a corrected lean4 code block."""
