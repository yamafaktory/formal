import Mathlib

namespace Verifier

theorem replace_proof_nothing_of_the_old_proof_survives.holds :
    replace_proof_nothing_of_the_old_proof_survives := by
  intro code tactic result h
  unfold replaceProof at h
  split_ifs at h
  obtain rfl := Option.some.inj h
  simp only [List.append_assoc]
  exact List.suffix_append _ _

end Verifier
