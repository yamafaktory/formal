import Mathlib

namespace Run

theorem parse_output_the_first_error_lean_reported_stays_first.holds :
    parse_output_the_first_error_lean_reported_stays_first := by
  intro hasSorry messages h
  simp only [errors]
  rcases List.exists_cons_of_ne_nil h with ⟨first, rest, hcons⟩
  rw [hcons]
  simp

end Run
