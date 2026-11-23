import Mathlib

namespace Verifier

theorem replace_all_for_leaves_text_without_the_pattern (pattern replacement : List Char) :
    ∀ (fuel : Nat) (s : List Char), ¬ pattern <:+: s →
      ProofCache.replaceAllFor pattern replacement fuel s = s := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ fuel ih =>
    intro s h
    cases s with
    | nil => rfl
    | cons c rest =>
      have hprefix : pattern.isPrefixOf (c :: rest) = false := by
        cases hp : pattern.isPrefixOf (c :: rest) with
        | false => rfl
        | true => exact absurd (List.isPrefixOf_iff_prefix.mp hp).isInfix h
      have hrest : ¬ pattern <:+: rest := fun hin =>
        h (hin.trans (List.suffix_cons c rest).isInfix)
      simp [ProofCache.replaceAllFor, hprefix, ih rest hrest]

theorem with_auto_tactics_text_without_a_placeholder_is_untouched.holds :
    with_auto_tactics_text_without_a_placeholder_is_untouched := by
  intro s hfirst hsecond
  unfold withAutoTactics ProofCache.replaceAll
  rw [replace_all_for_leaves_text_without_the_pattern _ _ _ s hfirst]
  rw [replace_all_for_leaves_text_without_the_pattern _ _ _ s hsecond]

end Verifier
