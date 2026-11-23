import Mathlib

namespace Run

theorem parse_output_a_sorry_warning_is_never_a_success.holds :
    parse_output_a_sorry_warning_is_never_a_success := by
  intro isSorryDeclaration hasSorry messages code message hmem hwarning hsorry
  have hin : { message with severity := "error".toList } ∈ promotedSorries hasSorry messages := by
    simp only [promotedSorries, List.mem_map]
    refine ⟨message, List.mem_filter.mpr ⟨hmem, ?_⟩, rfl⟩
    rw [hwarning, hsorry]
    decide
  have hne : errors isSorryDeclaration hasSorry messages ≠ [] := by
    intro h
    have : promotedSorries hasSorry messages = [] := by
      simp only [errors, List.append_eq_nil_iff] at h
      exact h.2
    rw [this] at hin
    simp at hin
  simp only [success, Bool.and_eq_false_iff, List.isEmpty_eq_false_iff_exists_mem]
  right
  exact List.exists_mem_of_ne_nil _ hne

end Run
