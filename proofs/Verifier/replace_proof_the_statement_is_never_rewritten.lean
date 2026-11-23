import Mathlib

namespace Verifier

theorem replace_proof_the_statement_is_never_rewritten.holds :
    replace_proof_the_statement_is_never_rewritten := by
  intro code tactic result h
  unfold replaceProof at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  simp only [List.append_assoc]
  exact List.prefix_append _ _

end Verifier
