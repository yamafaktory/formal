import Mathlib

namespace Pystr

theorem go_cons_plain (c : Char) (hc : isBreak c = false) (line rest : List Char) :
    splitlines.go line (c :: rest) = splitlines.go (line ++ [c]) rest := by
  have hcr : c ≠ '\r' := by
    rintro rfl
    simp [isBreak] at hc
  rw [splitlines.go.eq_3 _ _ _ (fun _ h _ => hcr h)]
  simp [hc]

theorem go_prefix (a : List Char) (h : ∀ c ∈ a, isBreak c = false) :
    ∀ line t, splitlines.go line (a ++ t) = splitlines.go (line ++ a) t := by
  induction a with
  | nil => simp
  | cons c a ih =>
    intro line t
    rw [List.cons_append, go_cons_plain c (h c (by simp)),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

theorem splitlines_crlf_is_one_boundary.holds : splitlines_crlf_is_one_boundary := by
  intro a h b
  unfold splitlines
  rw [go_prefix a h [] ('\r' :: '\n' :: b)]
  simp [splitlines.go]

end Pystr
