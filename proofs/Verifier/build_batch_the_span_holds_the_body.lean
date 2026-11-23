import Mathlib

namespace Verifier

theorem build_batch_the_span_holds_the_body.holds : build_batch_the_span_holds_the_body := by
  intro before namespaceLine endLine body j hj
  have hfirst : firstLine before.length + j - 1 = before.length + (1 + j) := by
    unfold firstLine
    omega
  rw [hfirst, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [show 1 + j = j + 1 from by omega]
  simp only [List.getElem?_cons_succ]
  rw [List.getElem?_append_left hj]

end Verifier
