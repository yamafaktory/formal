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

theorem rstrip_decomp (s : List Char) :
    ∃ z, s = rstrip s ++ z ∧ ∀ c ∈ z, isSpace c = true := by
  obtain ⟨z, hz, hzp⟩ := dropWhile_decomp s.reverse
  refine ⟨z.reverse, ?_, fun c hc => hzp c (List.mem_reverse.mp hc)⟩
  simpa [rstrip] using congrArg List.reverse hz

theorem rstrip_last (s t : List Char) (c : Char) (h : rstrip s = t ++ [c]) :
    isSpace c = false := by
  have h2 : s.reverse.dropWhile isSpace = c :: t.reverse := by
    simpa [rstrip] using congrArg List.reverse h
  exact dropWhile_head s.reverse c t.reverse h2

theorem strip_head (s : List Char) (c : Char) (t : List Char) (h : strip s = c :: t) :
    isSpace c = false := by
  obtain ⟨suf, hsuf, _⟩ := rstrip_decomp (s.dropWhile isSpace)
  have hx : s.dropWhile isSpace = c :: (t ++ suf) := by
    unfold strip at h
    rw [hsuf, h, List.cons_append]
  exact dropWhile_head s c (t ++ suf) hx

theorem strip_ends_are_not_space.holds : strip_ends_are_not_space :=
  fun s => ⟨strip_head s, fun t c h => rstrip_last (s.dropWhile isSpace) t c h⟩

end Pystr
