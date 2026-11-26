theorem Sum.total_append.holds : Sum.total_append := by
  intro a b
  induction a with
  | nil => simp [Sum.total]
  | cons x xs ih => simp [Sum.total]
