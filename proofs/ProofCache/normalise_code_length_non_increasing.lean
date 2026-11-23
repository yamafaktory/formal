import Mathlib

namespace ProofCache

theorem rstrip_length_le (l : List Char) : (Pystr.rstrip l).length ≤ l.length := by
  simp only [Pystr.rstrip, List.length_reverse]
  exact le_trans (List.length_dropWhile_le _ _) (by simp)

theorem strip_length_le (l : List Char) : (Pystr.strip l).length ≤ l.length :=
  le_trans (rstrip_length_le _) (List.length_dropWhile_le _ _)

theorem intercalate_map_rstrip_le (ls : List (List Char)) :
    (['\n'].intercalate (ls.map Pystr.rstrip)).length ≤ (['\n'].intercalate ls).length := by
  induction ls with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simpa [List.intercalate] using rstrip_length_le a
    | cons b u =>
      simp only [List.intercalate, List.map_cons, List.intersperse_cons_cons, List.flatten_cons,
        List.length_append] at ih ⊢
      have := rstrip_length_le a
      omega

theorem intercalate_cons_le (x : List Char) (ls : List (List Char)) :
    (['\n'].intercalate (x :: ls)).length ≤ x.length + 1 + (['\n'].intercalate ls).length := by
  cases ls with
  | nil => simp [List.intercalate]
  | cons y t =>
    simp only [List.intercalate, List.intersperse_cons_cons, List.flatten_cons,
      List.length_append, List.length_singleton]
    omega

theorem splitlines_go_length (line s : List Char) :
    (['\n'].intercalate (Pystr.splitlines.go line s)).length ≤ line.length + s.length := by
  induction line, s using Pystr.splitlines.go.induct with
  | case1 line h => simp [Pystr.splitlines.go, h, List.intercalate]
  | case2 line h => simp [Pystr.splitlines.go, h, List.intercalate]
  | case3 line rest ih =>
    have := intercalate_cons_le line (Pystr.splitlines.go [] rest)
    simp only [Pystr.splitlines.go, List.length_cons] at ih this ⊢
    simp at ih
    omega
  | case4 line c rest hcr hb ih =>
    have := intercalate_cons_le line (Pystr.splitlines.go [] rest)
    rw [Pystr.splitlines.go.eq_def]
    split
    · simp_all
    · simp_all
    · simp_all
      omega
  | case5 line c rest hcr hb ih =>
    rw [Pystr.splitlines.go.eq_def]
    split
    · simp_all
    · simp_all
    · simp_all
      omega

theorem normalise_code_length_non_increasing.holds : normalise_code_length_non_increasing := by
  intro s
  have h := intercalate_map_rstrip_le (Pystr.splitlines (Pystr.strip s))
  have g := splitlines_go_length [] (Pystr.strip s)
  simp only [List.length_nil, Nat.zero_add] at g
  exact le_trans h (le_trans g (strip_length_le s))

end ProofCache
