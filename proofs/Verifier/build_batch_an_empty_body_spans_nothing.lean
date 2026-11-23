import Mathlib

namespace Verifier

theorem build_batch_an_empty_body_spans_nothing.holds :
    build_batch_an_empty_body_spans_nothing := by
  intro before line
  unfold covers firstLine lastLine
  omega

end Verifier
