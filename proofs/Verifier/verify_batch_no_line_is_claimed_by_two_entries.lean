import Mathlib

namespace Verifier

theorem starts_after (bodies : List Nat) :
    ∀ (before : Nat) (span : Nat × Nat), span ∈ spans bodies before → before + 2 ≤ span.1 := by
  induction bodies with
  | nil => intro before span hs; simp [spans] at hs
  | cons body rest ih =>
    intro before span hs
    simp only [spans, List.mem_cons] at hs
    rcases hs with rfl | hs
    · simp [firstLine]
    · have := ih (before + body + 3) span hs
      omega

theorem verify_batch_no_line_is_claimed_by_two_entries.holds :
    verify_batch_no_line_is_claimed_by_two_entries := by
  intro bodies before body line span hs hhere
  have hlater := starts_after bodies (before + body + 3) span hs
  simp only [covers, firstLine, lastLine] at hhere ⊢
  omega

end Verifier
