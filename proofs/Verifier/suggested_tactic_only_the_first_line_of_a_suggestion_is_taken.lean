import Mathlib

namespace Verifier

theorem suggested_tactic_only_the_first_line_of_a_suggestion_is_taken.holds :
    suggested_tactic_only_the_first_line_of_a_suggestion_is_taken := by
  unfold suggested_tactic_only_the_first_line_of_a_suggestion_is_taken
  decide +kernel

end Verifier
