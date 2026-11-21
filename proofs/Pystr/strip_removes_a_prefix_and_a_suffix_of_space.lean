import Mathlib

namespace Pystr

theorem dropWhile_decomp (s : List Char) :
    ∃ z, s = z ++ s.dropWhile isSpace ∧ ∀ c ∈ z, isSpace c = true :=
  ⟨s.takeWhile isSpace, List.takeWhile_append_dropWhile.symm,
    fun c h => by simpa using (List.all_eq_true.mp List.all_takeWhile) c h⟩

theorem rstrip_decomp (s : List Char) :
    ∃ z, s = rstrip s ++ z ∧ ∀ c ∈ z, isSpace c = true := by
  obtain ⟨z, hz, hzp⟩ := dropWhile_decomp s.reverse
  refine ⟨z.reverse, ?_, fun c hc => hzp c (List.mem_reverse.mp hc)⟩
  simpa [rstrip] using congrArg List.reverse hz

theorem strip_removes_a_prefix_and_a_suffix_of_space.holds :
    strip_removes_a_prefix_and_a_suffix_of_space := by
  intro s
  obtain ⟨pre, hpre, hprep⟩ := dropWhile_decomp s
  obtain ⟨suf, hsuf, hsufp⟩ := rstrip_decomp (s.dropWhile isSpace)
  refine ⟨pre, suf, ?_, hprep, hsufp⟩
  rw [List.append_assoc, strip, ← hsuf]
  exact hpre

end Pystr
