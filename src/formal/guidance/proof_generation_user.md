Replace every `sorry` in this Lean 4 theorem with a real proof.

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

Output ONLY a lean4 code block with the proof filled in.
