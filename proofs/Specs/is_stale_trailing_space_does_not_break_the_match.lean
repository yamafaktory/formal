import Mathlib

namespace Specs

theorem is_stale_trailing_space_does_not_break_the_match.holds :
    is_stale_trailing_space_does_not_break_the_match := by
  unfold is_stale_trailing_space_does_not_break_the_match
  decide +kernel

end Specs
