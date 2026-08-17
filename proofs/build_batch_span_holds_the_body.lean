import Mathlib

-- Assumptions: the batch is modelled as a list of lines, and one entry's emission
-- as `before ++ namespace :: body ++ [end]`, which is what build_batch pushes.
-- Line numbers are 1-based, as Lean reports them, so `first` is
-- `before.length + 2` — the line after the namespace line.

def firstLine (before : Nat) : Nat := before + 2

def lastLine (before body : Nat) : Nat := before + 1 + body

def covers (first last line : Nat) : Prop := first ≤ line ∧ line ≤ last

theorem the_span_holds_the_body (before : List (List Char)) (ns endl : List Char)
    (body : List (List Char)) (j : Nat) (hj : j < body.length) :
    (before ++ ns :: (body ++ [endl]))[firstLine before.length + j - 1]? = body[j]? := by
  have hfirst : firstLine before.length + j - 1 = before.length + (1 + j) := by
    unfold firstLine
    omega
  rw [hfirst, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [show 1 + j = j + 1 from by omega]
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_left hj]
