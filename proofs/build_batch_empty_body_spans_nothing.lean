import Mathlib

-- Assumptions: the batch is modelled as a list of lines, and one entry's emission
-- as `before ++ namespace :: body ++ [end]`, which is what build_batch pushes.
-- Line numbers are 1-based, as Lean reports them, so `first` is
-- `before.length + 2` — the line after the namespace line.

def firstLine (before : Nat) : Nat := before + 2

def lastLine (before body : Nat) : Nat := before + 1 + body

def covers (first last line : Nat) : Prop := first ≤ line ∧ line ≤ last

theorem an_empty_body_spans_nothing (before line : Nat) :
    ¬ covers (firstLine before) (lastLine before 0) line := by
  unfold covers firstLine lastLine
  omega
