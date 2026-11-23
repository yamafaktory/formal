import Mathlib

namespace Hints

theorem lookup_a_table_nothing_claims_gives_the_fallback.holds :
    lookup_a_table_nothing_claims_gives_the_fallback := by
  intro fallback claims answer rules
  induction rules with
  | nil => intro _; rfl
  | cons rule rest ih =>
    intro h
    have hr : claims rule = false := h rule (by simp)
    simp only [lookup, hr, Bool.false_eq_true, if_false]
    exact ih (fun other hother => h other (by simp [hother]))

end Hints
