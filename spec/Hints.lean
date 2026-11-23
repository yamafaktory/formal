namespace Hints

def lookup (fallback : List Char) (claims : Nat → Bool) (answer : Nat → Option (List Char)) :
    List Nat → List Char
  | [] => fallback
  | rule :: rest =>
    if claims rule then
      match answer rule with
      | some hint => hint
      | none => lookup fallback claims answer rest
    else lookup fallback claims answer rest

def lookup_a_table_nothing_claims_gives_the_fallback : Prop :=
  ∀ fallback claims answer (rules : List Nat), (∀ rule ∈ rules, claims rule = false) →
    lookup fallback claims answer rules = fallback

def lookup_the_first_rule_that_answers_wins : Prop :=
  ∀ fallback claims answer rule rest hint, claims rule = true → answer rule = some hint →
    lookup fallback claims answer (rule :: rest) = hint

def lookup_a_rule_that_claims_without_answering_does_not_shadow : Prop :=
  ∀ fallback claims answer rule rest, claims rule = true → answer rule = none →
    lookup fallback claims answer (rule :: rest) = lookup fallback claims answer rest

end Hints
