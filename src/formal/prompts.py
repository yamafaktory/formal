"""The instructions formal serves to whoever is writing the properties and the Lean.

Rendered by guide.py and reachable at GET /guide/{topic}. Nothing here is called:
formal does not run a model. These are the accumulated rules for making the three
judgements it cannot make for you, and they are the reason it is worth asking rather
than improvising.
"""

AUTOFORMALIZE_SYSTEM = """You are a Lean 4 expert. Output ONLY valid Lean 4 code in a lean4 code block.
Use Lean 4 syntax — not Lean 3. All types must be from Lean 4 / Mathlib.

Model text as `List Char`, never as Lean's `String`. `String.startsWith` is implemented
through `String.Slice.Pattern.ForwardPattern`, `String.isPrefixOf` does not reduce, and
`String.mk` / `String.length` blow the recursion depth — goals stated over `String` are
not provable in practice. The same properties over `List Char` close with `simp`,
`List.isPrefixOf`, `List.prefix_append`, `List.append_inj` and `List.take_append`.

So write `def f (s : List Char) : List Char := ...` rather than taking a `String`, and
state the theorem over `List Char`. Use string literals only where the value is concrete
and never destructured."""

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
- For arithmetic goals (equality or inequality involving +, *, sum, etc.) NEVER use `constructor` —
  use `ring`, `linarith`, `omega`, or `simp [...]` with the relevant lemmas
- After case-splitting on an enum/inductive, residual goals of the form `0 < "x".length`
  or `"x".length = 1` are closed concrete propositions — use `decide` or `norm_num`, NOT `omega`.
  Use `all_goals decide` or `all_goals norm_num` to close all such goals at once.
- When a hypothesis `h : Except.ok X = Except.error Y` (or `h : some X = none`) is a contradiction,
  do NOT rely on bare `simp at h` — it may leave the goal open. Use instead:
    `exact absurd h (by simp)` or `simp [Except.ok.injEq] at h` or `cases h`
  These guarantee the branch is closed.
- For `iff` goals whose function uses `if cond then A else B`:
  · Forward direction (A = B → cond): `unfold f at h; split_ifs at h with hc; · exact hc; · simp [Except.ok.injEq] at h`
  · Backward direction (cond → f x = A): prefer `simp only [f, if_pos h]` in ONE step —
    do NOT `unfold f` then `rw [if_pos h]`; rw closes via rfl automatically and any tactic after will crash.
    Alternatively: `unfold f; split_ifs with hc; · rfl; · exact absurd h hc`
- For properties that hold for a specific enum/constructor value (e.g. `h : op = PLUS`):
  use `subst h` (if the variable appears alone) or `simp only [h]` to substitute the specific value
  everywhere, then `simp [PLUS.someField, ...]` to reduce the multi-branch if/match.
  Do NOT use `decide` or `aesop` on open inductive types — they will not terminate.
  Pattern:
    intro h          -- h : op = PLUS
    subst h          -- replaces all `op` with `PLUS`
    simp [PLUS.getPrecedence, PLUS.print, ...]   -- reduces branches
- In list-induction cons cases with `hweights : ∀ x ∈ hd :: tl, x = 0` (or similar), extract facts
  with `have h1 := hweights _ (by simp)` for the head and
  `have h2 : ∀ x ∈ tl, x = 0 := fun x hx => hweights x (by simp [hx])` for the tail,
  then apply the IH to the tail and close with `simp [h1, mul_zero, ih_result]` or `ring`
- For max/min bound proofs use: `exact le_max_left _ _`, `exact le_max_right _ _`,
  `exact min_le_left _ _`, `exact min_le_right _ _`
- For goals that are already a hypothesis, use `exact h` or `assumption`, not `constructor`
- Use `unfold f` instead of `simp [f]` when you want to expand without risking
  the goal being closed prematurely
- Use `omega` for linear arithmetic on Nat/Int
- Use `linarith` for linear arithmetic on ℚ/ℝ
- Use `decide` for decidable propositions on small finite types
- Use `induction n` for natural number induction
- NEVER use `List.head!` or `l[0]!` — they require an `Inhabited` instance that domain types
  rarely have. Use `List.head?` (returns `Option`) or case on the list structure instead.
- When accessing a field with dot notation, write `x.fieldName` with NO space before the dot.
  A space (`x .fieldName`) makes Lean parse it as function application and will fail.
- For Bool goals: `x = true` and `¬(x = false)` are NOT automatically interchangeable.
  Use `decide`, `cases x <;> simp`, or `simp [Bool.eq_true_iff_ne_false]` to normalise.
- If a hypothesis is `h : x.field = true` and the goal is `true = true`, do NOT write
  `exact h` — the field was already unfolded to `true`, so just use `rfl`. If the goal
  still contains the field name, use `simp [h]` to rewrite first.
- NEVER use square brackets for regular hypotheses in theorem signatures. Square brackets
  `[h : T]` are ONLY for typeclass arguments. For all other hypotheses use round brackets:
  `(h : op = PLUS)`, `(hn : n > 0)`, etc.
  Wrong: `theorem foo [h : op = PLUS]`  Right: `theorem foo (h : op = PLUS)`
- To unfold a local definition across both goal and hypotheses: `unfold f at *` or `simp only [f] at *`.
  If `simp [f]` makes no progress on a hypothesis `h`, try `unfold f at h` or `delta f at h`.
- `split_ifs at h with hcond` branch ordering depends on the guard shape:
  • Plain `if cond then body else none`:
      FIRST `·` = TRUE branch (real content)
      LAST  `·` = FALSE branch (none — close with `simp at h`)
  • Negated `if !boolField then none else body`:
      FIRST `·` = `!boolField = true` (bool is FALSE, function returns none — close with `simp at h`)
      SECOND `·` = real content
  Never put `simp at h` in the real-content branch — it may make no progress or leave goals unsolved.

Mathlib API reference — use EXACTLY these names, do not guess alternatives:

List:
  List.length_singleton    : [a].length = 1
  List.length_cons         : (a :: l).length = l.length + 1
  List.length_nil          : [].length = 0
  List.mem_singleton       : a ∈ [b] ↔ a = b
  List.mem_cons            : a ∈ b :: l ↔ a = b ∨ a ∈ l
  List.mem_cons_self       : a ∈ a :: l   (implicit args only — use `simp` or `exact List.mem_cons_self`)
  List.mem_nil_iff         : a ∈ ([] : List α) ↔ False
  List.mem_append          : a ∈ l ++ m ↔ a ∈ l ∨ a ∈ m
  List.head?_cons          : List.head? (a :: l) = some a
  List.head?_nil           : List.head? ([] : List α) = none
  List.getLast?_cons_nil   : List.getLast? [a] = some a
  List.nodup_singleton     : List.Nodup [a]
  List.singleton_append    : [a] ++ l = a :: l
  List.length_pos_of_ne_nil: l ≠ [] → 0 < l.length  (or use: List.length_pos)
  List.ne_nil_of_length_pos: 0 < l.length → l ≠ []
  List.mem_of_mem_filter   : a ∈ l.filter p → a ∈ l
  List.find?_mem           : List.find? p l = some a → a ∈ l

Option:
  Option.some_injective    : some a = some b → a = b
  Option.get_some          : Option.get (some a) h = a
  Option.isSome_iff_exists : o.isSome = true ↔ ∃ a, o = some a

Nat / Int arithmetic:
  Nat.succ_ne_zero         : Nat.succ n ≠ 0
  Nat.lt_irrefl            : ¬ n < n
  Nat.le_of_lt_succ        : n < m + 1 → n ≤ m
  Nat.pow_le_pow_right     : 0 < x → n ≤ m → x ^ n ≤ x ^ m   (Nat only — use this)
  pow_le_pow_left          : 0 ≤ a → a ≤ b → ∀ n, a ^ n ≤ b ^ n
  -- NOTE: bare `pow_le_pow_right` (no Nat. prefix) may not exist in this Mathlib version.
  -- For power monotonicity in ordered semirings, prefer the `gcongr` tactic — it closes
  -- `x^n ≤ x^m` automatically when `n ≤ m` and `1 ≤ x` are in context.
  pow_add                  : a ^ (m + n) = a ^ m * a ^ n
  pow_mul                  : a ^ (m * n) = (a ^ m) ^ n
  mul_pow                  : (a * b) ^ n = a ^ n * b ^ n
  one_pow                  : (1 : α) ^ n = 1
  pow_zero                 : a ^ 0 = 1
  pow_succ                 : a ^ (n + 1) = a ^ n * a
  eq_comm                  : a = b ↔ b = a   (NOT Nat.eq_comm — eq_comm works for all types)

Key tactic patterns:
- Destructure a length-1 list into a concrete singleton (do NOT use List.length_eq_one):
    cases l with
    | nil => simp at h
    | cons a t =>
      cases t with
      | nil => -- l is now [a]; continue proof
        ...
      | cons b t => simp [List.length_cons] at h  -- or: omega
- Prove membership after reducing to [a]:
    simp  -- preferred: handles membership goals automatically
    -- alternative: exact List.mem_cons_self  (NO arguments — all are implicit)
- For `f [a] ∈ [a]` where f returns the only element: after casing to [a],
  unfold f, then `simp [List.head?_cons, List.mem_singleton]`

Proof templates for membership goals (use these patterns directly):

(A) "result of singleton-guarded function ∈ input list" — case on the list, then simp:
    cases l with
    | nil => simp at h
    | cons a t =>
      cases t with
      | nil =>
        simp at h   -- simplifies h: result = a (or similar)
        subst h     -- replaces result with a everywhere
        simp        -- closes a ∈ [a]  ← ONLY simp here; List.mem_cons_self takes NO args
      | cons b t => simp [List.length_cons] at h  -- or: omega

(B) "result of List.find? on filtered list ∈ original list":
    have hmem_filter := List.find?_mem h       -- a ∈ l.filter p
    exact ⟨_, List.mem_of_mem_filter hmem_filter, rfl⟩

(C) "result of a negated-bool-guarded filter+match is a member of the original list"
    -- Function shape: if !boolField then none else match (list.filter pred) with | [s] => some s.field | _ => none
    -- IMPORTANT: split_ifs on `!bool` reverses branch order — first branch is the `none` branch:
    --   first  · hGuard: !boolField = true  (bool is FALSE) → h: none = some _ → simp at h
    --   second · hGuard: ¬(!boolField)      (bool is TRUE)  → match content
    unfold f at h
    split_ifs at h with hGuard
    · simp at h              -- none = some _ contradiction
    · generalize hf : list.filter pred = fl at h
      cases fl with
      | nil => simp at h
      | cons a t =>
        cases t with
        | nil =>
          simp at h          -- some a.field = some result  →  a.field = result
          exact ⟨a, List.mem_of_mem_filter (by rw [hf]; simp), h⟩
        | cons b rest => simp at h

Theorem to prove:
{theorem}

Output ONLY a lean4 code block with the proof filled in."""

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
- A function is STILL PURE if it takes interface or abstract class parameters and only READS from
  them (calls their getter/query methods). Reading from an interface argument is not a side effect.
  Example: `print(Expression left, Expression right)` that calls `left.getType()` and returns a
  String is pure — it has no I/O and no global state mutation.
- Private helper methods that compute strings, numbers, or booleans from their arguments are
  almost always pure — classify them as pure unless they explicitly do I/O or mutate state.
- If a function mixes pure and impure, extract just the pure computation as a new helper
- If nothing is pure, return empty pure_functions array
- Preserve the original {language} syntax when extracting pure function code

Feature code:
{code}"""

PROPERTY_EXTRACTION_SYSTEM = """You are an expert in formal verification and Lean 4.
Respond ONLY with valid JSON. No markdown, no explanation."""

PROPERTY_EXTRACTION_USER = """Given these pure {language} functions, identify properties worth verifying in Lean 4,
and assess each one for Lean formalizability in a single pass.

Pure functions:
{pure_functions}

Feature summary: {feature_summary}

A property is VERIFIABLE if:
- It can be expressed purely in terms of mathematical structures
  (numbers, lists, sets, booleans, strings with structural equality)
- Every type involved can be mapped to a concrete Lean 4 type:
    equality / comparison  →  = or ≤ on the relevant type
    membership             →  ∈ Finset / ∈ List
    optional / nullable    →  Option T
    text / string          →  List Char (NOT String — see the modeling note below)
    ordered collection     →  List T or Finset T
    map / dictionary       →  Finset (K × V) or a function K → Option V
- The proof does not require axioms about runtime behaviour
  (memory layout, JVM internals, hash codes, reference identity, etc.)

Modeling assumptions applied during verification:
- Floating-point types are modeled as Rat (rationals) — NaN, Inf, IEEE 754 rounding do not exist.
- Strings are modeled as List Char, not Lean's String. String equality is structural.
- Collections are modeled as Finset or List with standard membership.

A property is UNVERIFIABLE only if it fundamentally depends on something outside these models:
- Reference/pointer identity (not value equality)
- Runtime type information or reflection
- Hash codes or memory addresses
- External state, I/O, or time

String properties — verifiability rules:
- `startsWith` / `isPrefixOf` with free-variable strings: mark verifiable=true.
  Add to assumptions: "Strings modeled as List Char; proof via simp [List.isPrefixOf]"
- String injectivity WITHOUT a separator precondition (e.g. f(a,b) = prefix++a++mid++b is injective
  because prefix and mid are unique delimiters): mark verifiable=true.
  Add to assumptions: "Strings modeled as List Char; proof via List.append_inj"
- String injectivity WITH a separator precondition (the proof requires assuming the separator does
  NOT appear inside either input string): mark verifiable=FALSE.
  unverifiable_reason: "Separator-precondition string injectivity requires substring-absence reasoning
  that Lean/Mathlib cannot discharge within practical timeouts — always times out."

When in doubt, mark as verifiable — ordering, bounds, identity, idempotency, and
monotonicity properties are almost always verifiable under these models.

Return a JSON object:
{{
  "properties": [
    {{
      "id": "prop_1",
      "description": "human-readable property description",
      "function": "which pure function this applies to",
      "kind": "one of: bound, identity, monotonicity, commutativity, idempotency, invariant",
      "formal": "mathematical statement, e.g. forall x, f(x) <= x",
      "preconditions": ["what must hold on inputs, e.g. 'n > 0', 'list is non-empty'"],
      "assumptions": ["modeling assumptions, e.g. 'no overflow', 'elements are comparable', 'floats as rationals'"],
      "verifiable": true,
      "unverifiable_reason": ""
    }}
  ]
}}

Focus on properties that are mathematically precise and meaningful for correctness (not trivial).
Aim for 2-5 properties per pure function. Max 10 total.
Set verifiable=false and explain in unverifiable_reason only for properties that genuinely cannot
be modelled in Lean 4 under the assumptions above."""

PROPERTY_FORMALIZE_AND_PROVE_USER = """Formalize this property as a Lean 4 theorem AND provide a complete proof.
No sorry.

Source language: {language}
Function code:
{function_code}

Property:
- Description: {description}
- Formal statement: {formal}
- Kind: {kind}
- Preconditions: {preconditions}
- Assumptions: {assumptions}

The preconditions must appear as explicit hypotheses in the theorem signature (e.g. `(h : n > 0)`).
The assumptions must appear as comments above the theorem so they are auditable.

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
  List.mem_cons_self       : a ∈ a :: l   (implicit args only — use `simp` or `exact List.mem_cons_self`, NO args)
  List.head?_cons          : List.head? (a :: l) = some a
  List.head?_nil           : List.head? ([] : List α) = none
  List.length_pos_of_ne_nil: l ≠ [] → 0 < l.length
  List.mem_of_mem_filter   : a ∈ l.filter p → a ∈ l
  List.find?_mem           : List.find? p l = some a → a ∈ l
  List.countP_append       : List.countP p (l ++ m) = List.countP p l + List.countP p m
  Option.some_injective    : some a = some b → a = b

String length / prefix:
  String.length_append          : (s ++ t).length = s.length + t.length
  -- NOTE: `String.isPrefixOf_append_left`, `List.isPrefixOf_append_left`, and
  --        `String.isPrefixOf_iff` do NOT exist in Mathlib — do not use any of them.
  -- For literal lengths: use `show "foo".length = 3 from rfl` inline in simp only, then omega.
  --   simp only [String.length_append, show "PREFIX".length = N from rfl, ...]
  --   omega
  -- Do NOT use `simp [String.length]` — it recurses infinitely. `String.length_mk` does not exist. before omega
  -- NEVER call `omega` on goals with un-reduced String.length literal expressions
  -- For `p.isPrefixOf (p ++ rest) = true` — use this two-step pattern:
  --   simp only [String.isPrefixOf, String.toList_append]  -- converts to List.isPrefixOf level
  --   rfl                                                  -- kernel reduces char-by-char, closes goal
  -- String.isPrefixOf is @[extern] (not definitionally reducible); List.isPrefixOf IS.
  -- After simp only, rfl closes the goal even with free-variable suffixes.
  -- Do NOT use `decide` (needs ground terms) or `simp [List.isPrefixOf]` (can loop).

Modeling notes:
- NEVER model a simple collection wrapper (e.g. an aggregation class that just holds a list) as a
  Lean struct with a `.data` field. Instead, represent it directly as `List T` or `Finset T`.
  Struct wrappers cause Lean's `++` to differ from `List.append`, so lemmas like `List.countP_append`
  won't apply without extra unwrapping. Just use the list directly.
- For string injectivity (proving f(a,b) = f(a',b') → a=a' ∧ b=b' for a format function):
  reduce strings to `List Char` using `String.ext_iff` and `String.toList_append`, then use
  `List.append_inj h rfl` to strip a fixed prefix (gives `prefix=prefix ∧ rest_l=rest_r`, take `.2`),
  and get length equality via `congr_arg List.length` + omega before stripping a variable-length suffix.
  NOTE: `List.append_left_cancel`, `List.append_right_cancel`, and `List.append_inj_iff` do NOT exist.
  This is a hard property in Lean — prefer `ring`/`omega` when the property can be rephrased
  as arithmetic instead.
- Do NOT use `decide` on goals that contain free variables — it only works on closed, ground
  propositions. Do NOT combine `simp [String.startsWith, String.isPrefixOf]` with `decide` —
  the simp leaves free variables and decide will time out.
  For `p.isPrefixOf (p ++ rest) = true` or `(p ++ rest).startsWith p` goals:
    NOTE: `String.isPrefixOf_append_left`, `List.isPrefixOf_append_left`, `String.isPrefixOf_iff`,
    and `String.startsWith_iff_isPrefixOf` do NOT exist in Mathlib.
    String.isPrefixOf is @[extern] (C FFI) — NOT definitionally reducible. List.isPrefixOf IS.
    Use this two-step pattern:
    simp only [String.isPrefixOf, String.toList_append]
    rfl
    -- After simp only, the goal is at List.isPrefixOf level; Lean's kernel reduces char-by-char
    -- and rfl closes it even with free-variable suffixes.
    -- Do NOT use simp [List.isPrefixOf] — it can loop on this goal.
- Mathlib lemmas (e.g. `List.length_append`) are propositions, not functions. Apply them with
  `simp [List.length_append]` or `rw [List.length_append]` — never write `List.length_append l`.

Proof templates for common goals:

(A) "result of a singleton-guarded function is a member of the list"
    -- After casing to [a] and simplifying h to result = a:
    cases l with
    | nil => simp at h
    | cons a t =>
      cases t with
      | nil =>
        simp at h  -- simplifies to: result = a
        subst h    -- replaces result with a everywhere
        simp       -- closes: a ∈ [a]  ← use simp ONLY, never List.mem_cons_self with args
      | cons b t => simp [List.length_cons] at h  -- or: omega

(B) "result of List.find? on a filtered list belongs to the original list"
    -- h : List.find? p (l.filter q) = some a
    have hmem_filter : a ∈ l.filter q := List.find?_mem h
    have hmem : a ∈ l := List.mem_of_mem_filter hmem_filter
    exact ⟨a, hmem, rfl⟩  -- or whatever the goal shape requires

(C) "result of a negated-bool-guarded filter+match is a member of the original list"
    -- Function shape: if !boolField then none else match (list.filter pred) with | [s] => some s.field | _ => none
    -- IMPORTANT: split_ifs on `!bool` reverses branch order — first branch is the `none` branch:
    --   first  · hGuard: !boolField = true  (bool is FALSE) → h: none = some _ → simp at h
    --   second · hGuard: ¬(!boolField)      (bool is TRUE)  → match content
    unfold f at h
    split_ifs at h with hGuard
    · simp at h              -- none = some _ contradiction
    · generalize hf : list.filter pred = fl at h
      cases fl with
      | nil => simp at h
      | cons a t =>
        cases t with
        | nil =>
          simp at h          -- some a.field = some result  →  a.field = result
          exact ⟨a, List.mem_of_mem_filter (by rw [hf]; simp), h⟩
        | cons b rest => simp at h

(D) "format function is injective: PREFIX ++ w ++ SUFFIX = PREFIX ++ w' ++ SUFFIX → w = w'"
    -- Use List.append_inj (the ONLY reliable cancel lemma — left_cancel and right_cancel do not exist):
    --   String.ext_iff       : s = t ↔ s.toList = t.toList
    --   String.toList_append : (s ++ t).toList = s.toList ++ t.toList
    --   List.append_inj h hl : l₁ ++ r₁ = l₂ ++ r₂ → l₁.length = l₂.length → l₁ = l₂ ∧ r₁ = r₂
    --   NOTE: List.append_left_cancel and List.append_right_cancel do NOT exist in Mathlib.
    intro h
    -- Convert the String equality to List Char equality
    rw [String.ext_iff] at h
    simp only [String.toList_append] at h
    -- Reassociate so the fixed prefix is isolated on the left:
    simp only [List.append_assoc] at h
    -- Strip the fixed prefix: both sides start with "PREFIX".toList, so lengths are rfl:
    have h1 : w.toList ++ "SUFFIX".toList = w'.toList ++ "SUFFIX".toList :=
      (List.append_inj h rfl).2
    -- Strip the fixed suffix: need length equality of w.toList and w'.toList first:
    have hlen : w.toList.length = w'.toList.length := by
      have := congr_arg List.length h1
      simp [List.length_append] at this; omega
    have h2 : w.toList = w'.toList := (List.append_inj h1 hlen).1
    -- Conclude w = w':
    exact String.ext h2
    -- NOTE: this only works when there is NO ambiguous split point (i.e. the separator
    -- cannot appear inside w). If a separator precondition is needed, mark as unverifiable.

Output ONLY a lean4 code block with the complete theorem and proof."""

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
