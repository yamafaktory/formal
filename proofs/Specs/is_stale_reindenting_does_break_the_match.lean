import Mathlib

namespace Specs

theorem is_stale_reindenting_does_break_the_match.holds :
    is_stale_reindenting_does_break_the_match := by
  unfold is_stale_reindenting_does_break_the_match
  decide +kernel

end Specs
