namespace Sum

def total : List Nat → Nat
  | [] => 0
  | x :: xs => x + total xs

def total_append : Prop := ∀ a b : List Nat, total (a ++ b) = total a + total b

end Sum
