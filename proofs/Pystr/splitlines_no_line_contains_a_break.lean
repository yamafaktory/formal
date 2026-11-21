import Mathlib

namespace Pystr

theorem go_clean (line s : List Char) :
    (∀ x ∈ line, isBreak x = false) → ∀ l ∈ splitlines.go line s, ∀ x ∈ l, isBreak x = false := by
  induction line, s using splitlines.go.induct with
  | case1 line h =>
    intro _ l hl
    simp [splitlines.go, h] at hl
  | case2 line h =>
    intro hline l hl x hx
    simp [splitlines.go, h] at hl
    subst hl
    exact hline x hx
  | case3 line rest ih =>
    intro hline l hl x hx
    simp only [splitlines.go, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hline x hx
    · exact ih (by simp) l hl x hx
  | case4 line c rest hne hb ih =>
    intro hline l hl x hx
    rw [splitlines.go.eq_3 _ _ _ hne] at hl
    simp only [hb, ↓reduceIte, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact hline x hx
    · exact ih (by simp) l hl x hx
  | case5 line c rest hne hb ih =>
    intro hline l hl x hx
    rw [splitlines.go.eq_3 _ _ _ hne] at hl
    simp only [hb] at hl
    refine ih ?_ l hl x hx
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hline y hy
    · simp at hy
      subst hy
      simpa using hb

theorem splitlines_no_line_contains_a_break.holds : splitlines_no_line_contains_a_break :=
  fun s => go_clean [] s (by simp)

end Pystr
