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

theorem a_rule_that_claims_without_answering_does_not_shadow
    (fallback : List Char) (claims : Nat → Bool) (answer : Nat → Option (List Char))
    (r : Nat) (rest : List Nat) (hm : claims r = true) (ha : answer r = none) :
    lookup fallback claims answer (r :: rest) = lookup fallback claims answer rest := by
  simp only [lookup, hm, if_true, ha]
