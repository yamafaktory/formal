namespace Lists

def total : List Nat → Nat
  | [] => 0
  | x :: xs => x + total xs

def append_lengths : Prop :=
  ∀ a b c d : List Nat, a.length = b.length → c.length = d.length →
    (a ++ c).length = (b ++ d).length

def total_append : Prop := ∀ a b : List Nat, total (a ++ b) = total a + total b

end Lists
