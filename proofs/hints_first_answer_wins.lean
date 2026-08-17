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

theorem the_first_rule_that_answers_wins
    (fallback : List Char) (claims : Nat → Bool) (answer : Nat → Option (List Char))
    (r : Nat) (rest : List Nat) (hm : claims r = true) (hint : List Char)
    (ha : answer r = some hint) :
    lookup fallback claims answer (r :: rest) = hint := by
  simp only [lookup, hm, if_true, ha]

-- A rule that claims a diagnostic but produces nothing must not shadow the rules
-- below it: the walk continues past it rather than falling straight to the fallback.
