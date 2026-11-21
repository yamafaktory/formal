import Mathlib

namespace Pystr

theorem dropWhile_decomp (s : List Char) :
    ∃ z, s = z ++ s.dropWhile isSpace ∧ ∀ c ∈ z, isSpace c = true :=
  ⟨s.takeWhile isSpace, List.takeWhile_append_dropWhile.symm,
    fun c h => by simpa using (List.all_eq_true.mp List.all_takeWhile) c h⟩

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

theorem rstrip_decomp (s : List Char) :
    ∃ z, s = rstrip s ++ z ∧ ∀ c ∈ z, isSpace c = true := by
  obtain ⟨z, hz, hzp⟩ := dropWhile_decomp s.reverse
  refine ⟨z.reverse, ?_, fun c hc => hzp c (List.mem_reverse.mp hc)⟩
  simpa [rstrip] using congrArg List.reverse hz

theorem rstrip_idem (s : List Char) : rstrip (rstrip s) = rstrip s := by
  simp [rstrip, dropWhile_idem]

theorem strip_head (s : List Char) (c : Char) (t : List Char) (h : strip s = c :: t) :
    isSpace c = false := by
  obtain ⟨suf, hsuf, _⟩ := rstrip_decomp (s.dropWhile isSpace)
  have hx : s.dropWhile isSpace = c :: (t ++ suf) := by
    unfold strip at h
    rw [hsuf, h, List.cons_append]
  exact dropWhile_head s c (t ++ suf) hx

theorem strip_idempotent.holds : strip_idempotent := by
  intro s
  have h1 : (strip s).dropWhile isSpace = strip s := by
    cases hs : strip s with
    | nil => rfl
    | cons c t => exact List.dropWhile_cons_of_neg (by simp [strip_head s c t hs])
  rw [strip, h1, strip, rstrip_idem]

end Pystr
