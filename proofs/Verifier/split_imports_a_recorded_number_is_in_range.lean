import Mathlib

namespace Verifier

theorem in_range (isImport : List Char → Bool) :
    ∀ (lines : List (List Char)) (n number : Nat),
      number ∈ (split isImport lines n).2.2 → n ≤ number ∧ number < n + lines.length := by
  intro lines
  induction lines with
  | nil => intro n number hmem; simp [split] at hmem
  | cons line rest ih =>
    intro n number hmem
    rw [split] at hmem
    split_ifs at hmem with h
    · have := ih (n + 1) number hmem
      simp only [List.length_cons]
      omega
    · simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp only [List.length_cons]
        omega
      · have := ih (n + 1) number hmem
        simp only [List.length_cons]
        omega

theorem split_imports_a_recorded_number_is_in_range.holds :
    split_imports_a_recorded_number_is_in_range :=
  fun isImport => in_range isImport

end Verifier
