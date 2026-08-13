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
- For properties that hold for one constructor of a sum type (`h : mode = Fast`, `h : c = 'x'`,
  `h : tag = Leaf`): use `subst h` (if the variable appears alone) or `simp only [h]` to substitute
  that value everywhere, then `simp [theFunction]` to reduce the branch it selects.
  Do NOT use `decide` or `aesop` on open inductive types — they will not terminate.
  Pattern:
    intro h          -- h : mode = Fast
    subst h          -- replaces every `mode` with `Fast`
    simp [rateFor, labelFor]   -- reduces the match to the Fast branch
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
  `(h : mode = Fast)`, `(hn : n > 0)`, etc.
  Wrong: `theorem foo [h : mode = Fast]`  Right: `theorem foo (h : mode = Fast)`
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
  List.length_pos_of_ne_nil: l ≠ [] → 0 < l.length
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

DECOMPOSE_USER = """Separate the pure logic in the file from everything else.

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
- When you record a function's source in the spec file, copy it verbatim from the file"""

PROPERTY_EXTRACTION_SYSTEM = """You are an expert in formal verification and Lean 4.
Respond ONLY with valid JSON. No markdown, no explanation."""

PROPERTY_EXTRACTION_USER = """For each pure function you identified, work out the properties worth proving about it,
and assess each one for Lean formalizability in the same pass.

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
  (memory layout, allocator or GC behaviour, hash codes, pointer or reference identity,
  iteration order of an unordered collection, etc.)

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
- `startsWith` / `isPrefixOf` with free-variable strings: verifiable.
  Add to assumptions: "Strings modeled as List Char; proof via simp [List.isPrefixOf]"
- String injectivity WITHOUT a separator precondition (e.g. f(a,b) = prefix++a++mid++b is injective
  because prefix and mid are unique delimiters): verifiable.
  Add to assumptions: "Strings modeled as List Char; proof via List.append_inj"
- String injectivity WITH a separator precondition (the proof requires assuming the separator does
  NOT appear inside either input string): not verifiable. Substring-absence reasoning is not
  something Lean and Mathlib discharge within practical timeouts — it always times out.

When in doubt, treat it as verifiable — ordering, bounds, identity, idempotency, and
monotonicity properties are almost always verifiable under these models.

Write the ones you judge verifiable into the spec file described by GET /guide, and drop
the rest — there is no field for an unverifiable property, and nothing downstream reads
one. If leaving something out was a real decision, say so in your report to the user;
the spec file records what you are checking, not what you considered.

Each property needs a `kind`, which is one of:
  bound          a value is constrained — non-negative, within a range, never empty
  identity       two expressions are equal, or one rewrites to the other
  monotonicity   ordering is preserved: larger input, no smaller output
  commutativity  order of arguments or operations does not matter
  idempotency    applying twice is the same as applying once
  invariant      something is preserved or always holds — a count, a well-formedness
  counterexample two concrete inputs that must differ and do not, or must agree and do
                 not — a proven defect rather than a reassurance

Pick the one that describes the shape of the statement. `kind` is part of the cache key,
so use the same one for the same property across runs; when two fit, prefer the more
specific. Aim for 2-5 properties per pure function, at most 10 in total, and prefer
properties that would catch a real mistake over ones that restate the implementation.
"""

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
    strings          →  List Char (NOT String — see the note above on why)
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


FINITE_CASE_ANALYSIS = """Case analysis over Char, and what to do when Lean gives up rather than disagrees.

Two failures here are not Lean rejecting your proof — they are Lean running out of
budget. They report as `maximum recursion depth has been reached`, as a `simp` step
limit, or as no diagnostic at all. Raising the limit is almost never the fix: it
moves the failure, and pushed far enough it crashes the process instead of erroring.

`decide` over a membership goal
  A goal shaped `∀ c ∈ ['a', 'b', 'c'], P c` looks finite and decidable, and `decide`
  will try to prove it by evaluating a decision procedure over `Char` — a type with
  over a million inhabitants. It blows the recursion limit. Turn the membership into
  a disjunction of equalities first, then take the cases:

    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro c (rfl | rfl | rfl)
    all_goals rfl

  Each branch is now a ground proposition about one literal, which `rfl`, `decide` or
  `norm_num` closes instantly.

  The same applies one level up. A nested bounded quantifier over a table of pairs
  — `∀ p ∈ table, f p.1 = p.2` — is not small either; take the cases the same way:

    simp only [table, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    all_goals rfl

  Note `List.not_mem_nil` here where the single-list case above wants
  `List.mem_nil_iff`; both exist and they are not interchangeable.

Long `if`-chains over character literals
  `split_ifs` and `fin_cases` both hand the whole chain to `simp`, and a dozen
  branches over `Char` exhausts its step budget. Take the branches by hand:

    by_cases h : c = 'x'
    · rw [if_pos h]; ...
    · rw [if_neg h]; ...

  `rw [if_pos h]` and `rw [if_neg h]` reduce one condition at a time and cost nothing.
  This is longer to write and far cheaper to check.

Raising a limit
  `set_option maxRecDepth 4000 in` and `set_option maxHeartbeats 1000000 in` are
  accepted before a `theorem`. Reach for them only when you already understand which
  term is large and have decided it genuinely needs to be. If a proof needs a limit
  raised by an order of magnitude, the model is wrong, not the budget.

Preferring `simp only`
  Bare `simp` rewrites with everything in scope, which is both slow and unpredictable
  — it can rewrite the goal into a shape none of your later tactics expect. Naming the
  lemmas (`simp only [List.mem_cons, if_pos]`) keeps the goal where you left it."""


FILTER_AND_PARTITION = """Filtering and partitioning.

Selecting, rejecting and splitting a collection is the commonest shape of pure logic
there is, and the lemmas below are the ones that close those goals. Signatures are
from Lean v4.29 with Mathlib, checked rather than recalled — if you need something not
listed, reach for a tactic (`simp`, `induction`, `omega`) rather than guessing a name.

  List.filter_append   : filter p (l₁ ++ l₂) = filter p l₁ ++ filter p l₂
  List.filter_filter   : filter p (filter q l) = filter (fun a => p a && q a) l
  List.filter_cons     : filter p (x :: xs) = if p x then x :: filter p xs else filter p xs
  List.mem_filter      : x ∈ filter p as ↔ x ∈ as ∧ p x = true
  List.length_filter_le : (filter p l).length ≤ l.length
  List.filter_subset   : l₁ ⊆ l₂ → filter p l₁ ⊆ filter p l₂
  List.filter_eq_self  : filter p l = l ↔ ∀ a ∈ l, p a = true

  List.partition_eq_filter_filter : partition p l = (filter p l, filter (not ∘ p) l)

`partition` is defined by an accumulator, so induction on it directly is painful.
Rewrite with `List.partition_eq_filter_filter` first and prove the statement about the
two filters instead — that is what makes conservation properties tractable:

    rw [List.partition_eq_filter_filter]

A count is a filtered length: `List.countP_eq_length_filter` moves between them when a
property is easier to state one way and easier to prove the other."""
