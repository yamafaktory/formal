import Mathlib

namespace Verifier

theorem check_syntax_a_verdict_always_carries_its_reason.holds :
    check_syntax_a_verdict_always_carries_its_reason := by
  intro screen s
  have runs : ∀ found, runsReason found ≠ [] := fun _ =>
    List.append_ne_nil_of_left_ne_nil (by decide) _
  have empty : emptyReason ≠ [] := by decide
  have keyword : keywordReason ≠ [] := by decide
  unfold checkSyntax
  split_ifs <;> rcases screen s with _ | found <;> simp [runs, empty, keyword]

end Verifier
