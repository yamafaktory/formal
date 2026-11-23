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

theorem build_batch_every_span_starts_after_where_it_was_laid_out.holds :
    build_batch_every_span_starts_after_where_it_was_laid_out :=
  fun bodies => starts_after bodies

end Verifier
