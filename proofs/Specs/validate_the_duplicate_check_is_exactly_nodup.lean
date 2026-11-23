import Mathlib

namespace Specs

theorem validate_the_duplicate_check_is_exactly_nodup.holds :
    validate_the_duplicate_check_is_exactly_nodup := by
  intro ids
  rw [duplicates, List.filter_eq_nil_iff, List.nodup_iff_count_le_one]
  constructor
  · intro h a
    by_cases ha : a ∈ ids
    · have := h a ha
      simp only [decide_eq_true_eq, Nat.not_lt] at this
      exact this
    · simp [List.count_eq_zero_of_not_mem ha]
  · intro h a _
    have := h a
    simp only [decide_eq_true_eq, Nat.not_lt]
    exact this

end Specs
