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

theorem a_recorded_number_is_in_range (p : List Char → Bool) :
    ∀ (ls : List (List Char)) (n num : Nat),
      num ∈ (split p ls n).2.2 → n ≤ num ∧ num < n + ls.length := by
  intro ls
  induction ls with
  | nil => intro n num hmem; simp [split] at hmem
  | cons l rest ih =>
    intro n num hmem
    rw [split] at hmem
    split_ifs at hmem with h
    · have := ih (n + 1) num hmem
      simp only [List.length_cons]
      omega
    · simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp only [List.length_cons]
        omega
      · have := ih (n + 1) num hmem
        simp only [List.length_cons]
        omega
