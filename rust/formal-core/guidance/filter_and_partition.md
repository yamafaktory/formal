Filtering and partitioning.

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
property is easier to state one way and easier to prove the other.
