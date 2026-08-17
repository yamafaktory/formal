import Mathlib

-- Assumptions: a line is a List Char and a file a List of them; the classifier
-- `p` (in the Rust, `line.trim_start().starts_with("import ")`) is left abstract,
-- so every claim holds whatever counts as an import. `n` is the number given to
-- the first line, so the Rust's call is `split p ls 1`.

def split (p : List Char → Bool) :
    List (List Char) → Nat → List (List Char) × List (List Char) × List Nat
  | [], _ => ([], [], [])
  | l :: rest, n =>
      if p l then
        (l :: (split p rest (n + 1)).1, (split p rest (n + 1)).2.1, (split p rest (n + 1)).2.2)
      else
        ((split p rest (n + 1)).1, l :: (split p rest (n + 1)).2.1, n :: (split p rest (n + 1)).2.2)

theorem conservation (p : List Char → Bool) :
    ∀ (ls : List (List Char)) (n : Nat),
      (split p ls n).1.length + (split p ls n).2.1.length = ls.length := by
  intro ls
  induction ls with
  | nil => intro n; simp [split]
  | cons l rest ih =>
    intro n
    have hr := ih (n + 1)
    rw [split]
    split_ifs with h
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega
