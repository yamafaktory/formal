theorem Ring.in_range.holds : Ring.in_range := by
  intro index size h
  unfold Ring.wrap
  omega
