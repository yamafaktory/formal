namespace Discount

def discounted (price rate : Int) : Int := price * (1 - rate)

def never_negative : Prop :=
  ∀ price rate : Int, 0 ≤ price → 0 ≤ rate → rate ≤ 1 → 0 ≤ discounted price rate

def never_above_price : Prop :=
  ∀ price rate : Int, 0 ≤ rate → discounted price rate ≤ price

end Discount
