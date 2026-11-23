import Mathlib

namespace Run

theorem parse_output_a_nonzero_exit_is_never_a_success.holds :
    parse_output_a_nonzero_exit_is_never_a_success := by
  intro code errors h
  simp [success, h]

end Run
