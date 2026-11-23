import Mathlib

namespace Run

theorem parse_output_every_promoted_sorry_is_reported_as_an_error.holds :
    parse_output_every_promoted_sorry_is_reported_as_an_error := by
  intro hasSorry messages message h
  simp only [promotedSorries, List.mem_map] at h
  obtain ⟨original, _, rfl⟩ := h
  rfl

end Run
