import Mathlib

namespace Verifier

theorem suggested_tactic_trimming_quotes_does_not_eat_a_trailing_n.holds :
    suggested_tactic_trimming_quotes_does_not_eat_a_trailing_n := by
  unfold suggested_tactic_trimming_quotes_does_not_eat_a_trailing_n
  decide +kernel

end Verifier
