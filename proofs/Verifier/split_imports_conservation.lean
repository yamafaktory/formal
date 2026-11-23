import Mathlib

namespace Verifier

theorem split_imports_conservation.holds : split_imports_conservation := by
  intro isImport lines
  induction lines with
  | nil => intro n; simp [split]
  | cons line rest ih =>
    intro n
    have hr := ih (n + 1)
    rw [split]
    split_ifs with h
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

end Verifier
