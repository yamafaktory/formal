import Mathlib

namespace Verifier

theorem split_imports_every_body_line_is_numbered.holds :
    split_imports_every_body_line_is_numbered := by
  intro isImport lines
  induction lines with
  | nil => intro n; simp [split]
  | cons line rest ih =>
    intro n
    have hr := ih (n + 1)
    rw [split]
    split_ifs with h
    · exact hr
    · simp only [List.length_cons, hr]

end Verifier
