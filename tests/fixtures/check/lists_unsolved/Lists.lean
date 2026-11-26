namespace Lists

def append_lengths : Prop :=
  ∀ a b c d : List Nat, a.length = b.length → c.length = d.length →
    (a ++ c).length = (b ++ d).length

end Lists
