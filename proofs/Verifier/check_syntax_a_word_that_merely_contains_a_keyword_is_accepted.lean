import Mathlib

namespace Verifier

theorem check_syntax_a_word_that_merely_contains_a_keyword_is_accepted.holds :
    check_syntax_a_word_that_merely_contains_a_keyword_is_accepted := by
  intro screen h
  simp only [checkSyntax, h]
  decide +kernel

end Verifier
