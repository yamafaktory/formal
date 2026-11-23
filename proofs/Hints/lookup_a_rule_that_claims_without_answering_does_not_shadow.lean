import Mathlib

namespace Hints

theorem lookup_a_rule_that_claims_without_answering_does_not_shadow.holds :
    lookup_a_rule_that_claims_without_answering_does_not_shadow := by
  intro fallback claims answer rule rest hclaims hanswer
  simp only [lookup, hclaims, if_true, hanswer]

end Hints
