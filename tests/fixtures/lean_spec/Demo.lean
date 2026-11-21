namespace Demo

def double (n : Nat) : Nat := n + n

def double_even : Prop :=
  ∀ n, double n % 2 = 0

def double_mono : Prop := ∀ a b, a ≤ b → double a ≤ double b

end Demo
