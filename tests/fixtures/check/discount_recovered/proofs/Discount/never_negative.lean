import Mathlib

theorem Discount.never_negative.holds : Discount.never_negative := by
  intro price rate hp h0 h1
  unfold Discount.discounted
  linarith
