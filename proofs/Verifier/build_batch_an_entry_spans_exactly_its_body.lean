import Mathlib

namespace Verifier

theorem build_batch_an_entry_spans_exactly_its_body.holds :
    build_batch_an_entry_spans_exactly_its_body := by
  intro before body h
  unfold lastLine firstLine
  omega

end Verifier
