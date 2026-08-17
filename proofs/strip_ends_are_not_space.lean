import Mathlib

def lstrip (p : Char → Bool) : List Char → List Char
  | [] => []
  | c :: cs => if p c then lstrip p cs else c :: cs

def rstrip (p : Char → Bool) (s : List Char) : List Char :=
  (lstrip p s.reverse).reverse

def strip (p : Char → Bool) (s : List Char) : List Char :=
  rstrip p (lstrip p s)

theorem lstrip_decomp (p : Char → Bool) :
    ∀ s : List Char, ∃ z, s = z ++ lstrip p s ∧ ∀ c ∈ z, p c = true := by
  intro s
  induction s with
  | nil => exact ⟨[], by simp [lstrip], by simp⟩
  | cons a as ih =>
    by_cases h : p a
    · obtain ⟨z, hz, hzp⟩ := ih
      refine ⟨a :: z, ?_, ?_⟩
      · have hu : lstrip p (a :: as) = lstrip p as := by simp [lstrip, h]
        rw [hu, List.cons_append, ← hz]
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact h
        · exact hzp c hc'
    · refine ⟨[], ?_, by simp⟩
      simp [lstrip, h]

theorem lstrip_head (p : Char → Bool) :
    ∀ (s : List Char) (c : Char) (t : List Char), lstrip p s = c :: t → p c = false := by
  intro s
  induction s with
  | nil => intro c t h; simp [lstrip] at h
  | cons a as ih =>
    intro c t h
    by_cases hp : p a
    · rw [show lstrip p (a :: as) = lstrip p as from by simp [lstrip, hp]] at h
      exact ih c t h
    · rw [show lstrip p (a :: as) = a :: as from by simp [lstrip, hp]] at h
      have hac : a = c := ((List.cons.injEq a as c t).mp h).1
      rw [← hac]
      simpa using hp

theorem lstrip_idem (p : Char → Bool) (s : List Char) :
    lstrip p (lstrip p s) = lstrip p s := by
  induction s with
  | nil => simp [lstrip]
  | cons a as ih =>
    by_cases hp : p a
    · simp [lstrip, hp, ih]
    · simp [lstrip, hp]

theorem rstrip_decomp (p : Char → Bool) (s : List Char) :
    ∃ z, s = rstrip p s ++ z ∧ ∀ c ∈ z, p c = true := by
  obtain ⟨z, hz, hzp⟩ := lstrip_decomp p s.reverse
  refine ⟨z.reverse, ?_, ?_⟩
  · have hr := congrArg List.reverse hz
    simpa [rstrip] using hr
  · intro c hc
    exact hzp c (List.mem_reverse.mp hc)

theorem rstrip_last (p : Char → Bool) (s t : List Char) (c : Char)
    (h : rstrip p s = t ++ [c]) : p c = false := by
  have hr := congrArg List.reverse h
  have h2 : lstrip p s.reverse = c :: t.reverse := by simpa [rstrip] using hr
  exact lstrip_head p s.reverse c t.reverse h2

theorem rstrip_idem (p : Char → Bool) (s : List Char) :
    rstrip p (rstrip p s) = rstrip p s := by
  simp [rstrip, lstrip_idem]

theorem strip_head (p : Char → Bool) (s : List Char) (c : Char) (t : List Char)
    (h : strip p s = c :: t) : p c = false := by
  obtain ⟨suf, hsuf, _⟩ := rstrip_decomp p (lstrip p s)
  have hx : lstrip p s = c :: (t ++ suf) := by
    unfold strip at h
    rw [hsuf, h, List.cons_append]
  exact lstrip_head p s c (t ++ suf) hx

-- Assumptions: text modelled as List Char; trim_matches modelled as dropping a
-- maximal run from each end; quantified over the trimming predicate p, so it holds
-- for pystr::is_space in particular. An empty result satisfies both halves
-- vacuously — there is no first or last character to be space.

theorem strip_ends_are_not_space (p : Char → Bool) (s : List Char) :
    (∀ (c : Char) (t : List Char), strip p s = c :: t → p c = false) ∧
      (∀ (t : List Char) (c : Char), strip p s = t ++ [c] → p c = false) := by
  refine ⟨fun c t h => strip_head p s c t h, fun t c h => ?_⟩
  exact rstrip_last p (lstrip p s) t c h
