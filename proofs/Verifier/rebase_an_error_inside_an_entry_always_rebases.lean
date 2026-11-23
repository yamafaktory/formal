import Mathlib

namespace Verifier

theorem rebase_an_error_inside_an_entry_always_rebases.holds :
    rebase_an_error_inside_an_entry_always_rebases := by
  intro before body line h
  simp only [covers, firstLine, lastLine] at h
  simp only [firstLine]
  omega

end Verifier
