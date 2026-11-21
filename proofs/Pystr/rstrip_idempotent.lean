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

theorem dropWhile_idem (s : List Char) :
    (s.dropWhile isSpace).dropWhile isSpace = s.dropWhile isSpace := by
  cases h : s.dropWhile isSpace with
  | nil => rfl
  | cons c t => exact List.dropWhile_cons_of_neg (by simp [dropWhile_head s c t h])

theorem rstrip_idem (s : List Char) : rstrip (rstrip s) = rstrip s := by
  simp [rstrip, dropWhile_idem]

theorem rstrip_idempotent.holds : rstrip_idempotent :=
  rstrip_idem

end Pystr
