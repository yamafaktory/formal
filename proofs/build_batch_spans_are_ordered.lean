import Mathlib

-- Assumptions: an entry is modelled by the length of its body, and the batch by
-- the lengths in order. build_batch emits, per entry, a namespace line, the body,
-- an end line and a blank, so the next entry's `before` is this one's plus its
-- body plus three. Line numbers are 1-based, as Lean reports them.

def spans : List Nat → Nat → List (Nat × Nat)
  | [], _ => []
  | m :: rest, k => (k + 2, k + 1 + m) :: spans rest (k + m + 3)

def covers (s : Nat × Nat) (line : Nat) : Prop := s.1 ≤ line ∧ line ≤ s.2

theorem every_span_starts_after_where_it_was_laid_out :
    ∀ (ms : List Nat) (k : Nat) (s : Nat × Nat), s ∈ spans ms k → k + 2 ≤ s.1 := by
  intro ms
  induction ms with
  | nil => intro k s hs; simp [spans] at hs
  | cons m rest ih =>
    intro k s hs
    simp only [spans, List.mem_cons] at hs
    rcases hs with rfl | hs
    · omega
    · have := ih (k + m + 3) s hs
      omega
