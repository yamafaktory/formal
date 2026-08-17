import Mathlib

-- Assumptions: a rule is identified by its position in the table; whether a rule
-- claims a diagnostic (`claims`) and whether it produces advice (`answer`, which
-- descends into sub-rules in the Rust) are left abstract. The table is walked in
-- order, which is what makes order the semantics.

def lookup (fallback : List Char) (claims : Nat → Bool) (answer : Nat → Option (List Char)) :
    List Nat → List Char
  | [] => fallback
  | r :: rest =>
      if claims r then
        match answer r with
        | some hint => hint
        | none => lookup fallback claims answer rest
      else lookup fallback claims answer rest

theorem a_table_nothing_claims_gives_the_fallback
    (fallback : List Char) (claims : Nat → Bool) (answer : Nat → Option (List Char)) :
    ∀ rules : List Nat, (∀ r ∈ rules, claims r = false) →
      lookup fallback claims answer rules = fallback := by
  intro rules
  induction rules with
  | nil => intro _; rfl
  | cons r rest ih =>
    intro h
    have hr : claims r = false := h r (by simp)
    simp only [lookup, hr, if_false]
    exact ih (fun x hx => h x (by simp [hx]))
