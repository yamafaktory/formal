import Mathlib

namespace Pystr

theorem dropWhile_head (s : List Char) (c : Char) (t : List Char)
    (h : s.dropWhile isSpace = c :: t) : isSpace c = false := by
  induction s with
  | nil => simp at h
  | cons a as ih =>
    by_cases hp : isSpace a
    · rw [List.dropWhile_cons_of_pos hp] at h
      exact ih h
    · rw [List.dropWhile_cons_of_neg hp] at h
      cases h
      simpa using hp

theorem rstrip_last (s t : List Char) (c : Char) (h : rstrip s = t ++ [c]) :
    isSpace c = false := by
  have h2 : s.reverse.dropWhile isSpace = c :: t.reverse := by
    simpa [rstrip] using congrArg List.reverse h
  exact dropWhile_head s.reverse c t.reverse h2

theorem rstrip_never_ends_in_space.holds : rstrip_never_ends_in_space :=
  rstrip_last

end Pystr
