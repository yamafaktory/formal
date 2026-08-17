import Mathlib

-- Assumptions: the batch is modelled as a list of lines, and one entry's emission
-- as `before ++ namespace :: body ++ [end]`, which is what build_batch pushes.
-- Line numbers are 1-based, as Lean reports them, so `first` is
-- `before.length + 2` — the line after the namespace line.

def firstLine (before : Nat) : Nat := before + 2

def lastLine (before body : Nat) : Nat := before + 1 + body

def covers (first last line : Nat) : Prop := first ≤ line ∧ line ≤ last

theorem an_error_inside_an_entry_always_rebases (before body line : Nat)
    (h : covers (firstLine before) (lastLine before body) line) :
    line - firstLine before < body := by
  simp only [covers, firstLine, lastLine] at h
  simp only [firstLine]
  omega
