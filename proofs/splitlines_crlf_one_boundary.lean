import Mathlib

def isBreak (c : Char) : Bool :=
  c = '\n' || c = '\x0b' || c = '\x0c' || c = '\x1c' || c = '\x1d' || c = '\x1e' ||
    c = '\r' || c = '\x85' || c = '\u2028' || c = '\u2029'

def go : List Char → List Char → List (List Char)
  | [], acc => if acc = [] then [] else [acc]
  | [c], acc => if isBreak c then [acc] else [acc ++ [c]]
  | c :: d :: rest, acc =>
      if c = '\r' ∧ d = '\n' then acc :: go rest []
      else if isBreak c then acc :: go (d :: rest) []
      else go (d :: rest) (acc ++ [c])

def splitlines (s : List Char) : List (List Char) := go s []

theorem go_cons_plain (c : Char) (hc : isBreak c = false) (rest acc : List Char) :
    go (c :: rest) acc = go rest (acc ++ [c]) := by
  have hcr : ¬ (c = '\r') := by
    intro hh
    rw [hh] at hc
    simp [isBreak] at hc
  cases rest with
  | nil => simp [go, hc]
  | cons d rest' => simp [go, hc, hcr]

theorem go_prefix : ∀ (a : List Char), (∀ c ∈ a, isBreak c = false) →
    ∀ (t acc : List Char), go (a ++ t) acc = go t (acc ++ a) := by
  intro a
  induction a with
  | nil => intro _ t acc; simp
  | cons c a' ih =>
    intro h t acc
    have hc : isBreak c = false := h c (by simp)
    have h' : ∀ x ∈ a', isBreak x = false := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.cons_append, go_cons_plain c hc, ih h' t (acc ++ [c])]
    simp

theorem go_clean : ∀ (n : Nat) (s acc : List Char), s.length ≤ n →
    (∀ x ∈ acc, isBreak x = false) → ∀ l ∈ go s acc, ∀ x ∈ l, isBreak x = false := by
  intro n
  induction n with
  | zero =>
    intro s acc hlen hacc l hl x hx
    have hs : s = [] := by
      cases s with
      | nil => rfl
      | cons a as => simp at hlen
    subst hs
    by_cases hnil : acc = []
    · rw [show go ([] : List Char) acc = [] from by simp [go, hnil]] at hl
      simp at hl
    · rw [show go ([] : List Char) acc = [acc] from by simp [go, hnil]] at hl
      rw [List.mem_singleton] at hl
      subst hl
      exact hacc x hx
  | succ n ih =>
    intro s acc hlen hacc l hl x hx
    rcases s with _ | ⟨c, cs⟩
    · by_cases hnil : acc = []
      · rw [show go ([] : List Char) acc = [] from by simp [go, hnil]] at hl
        simp at hl
      · rw [show go ([] : List Char) acc = [acc] from by simp [go, hnil]] at hl
        rw [List.mem_singleton] at hl
        subst hl
        exact hacc x hx
    · rcases cs with _ | ⟨d, rest⟩
      · by_cases hb : isBreak c
        · rw [show go [c] acc = [acc] from by simp [go, hb]] at hl
          rw [List.mem_singleton] at hl
          subst hl
          exact hacc x hx
        · rw [show go [c] acc = [acc ++ [c]] from by simp [go, hb]] at hl
          rw [List.mem_singleton] at hl
          subst hl
          rcases List.mem_append.mp hx with h1 | h1
          · exact hacc x h1
          · rw [List.mem_singleton] at h1
            subst h1
            simpa using hb
      · have hrest : rest.length ≤ n := by
          simp only [List.length_cons] at hlen
          omega
        have hdrest : (d :: rest).length ≤ n := by
          simp only [List.length_cons] at hlen ⊢
          omega
        by_cases hcrlf : c = '\r' ∧ d = '\n'
        · rw [show go (c :: d :: rest) acc = acc :: go rest [] from by simp [go, hcrlf]] at hl
          rcases List.mem_cons.mp hl with rfl | hl2
          · exact hacc x hx
          · exact ih rest [] hrest (by simp) l hl2 x hx
        · by_cases hb : isBreak c
          · rw [show go (c :: d :: rest) acc = acc :: go (d :: rest) [] from by
              simp [go, hcrlf, hb]] at hl
            rcases List.mem_cons.mp hl with rfl | hl2
            · exact hacc x hx
            · exact ih (d :: rest) [] hdrest (by simp) l hl2 x hx
          · rw [show go (c :: d :: rest) acc = go (d :: rest) (acc ++ [c]) from by
              simp [go, hcrlf, hb]] at hl
            refine ih (d :: rest) (acc ++ [c]) hdrest ?_ l hl x hx
            intro y hy
            rcases List.mem_append.mp hy with h1 | h1
            · exact hacc y h1
            · rw [List.mem_singleton] at h1
              subst h1
              simpa using hb

-- Assumptions: text modelled as List Char, and a line as the List Char between two
-- boundaries; the boundary set is the ten characters the Rust match names.

theorem crlf_is_one_boundary (a : List Char) (h : ∀ c ∈ a, isBreak c = false)
    (b : List Char) :
    splitlines (a ++ '\r' :: '\n' :: b) = a :: splitlines b := by
  unfold splitlines
  rw [go_prefix a h ('\r' :: '\n' :: b) []]
  simp [go]
