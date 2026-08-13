Case analysis over Char, and what to do when Lean gives up rather than disagrees.

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
  lemmas (`simp only [List.mem_cons, if_pos]`) keeps the goal where you left it.
