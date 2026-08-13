Formalize this property as a Lean 4 theorem AND provide a complete proof.
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

Output ONLY a lean4 code block with the complete theorem and proof.
