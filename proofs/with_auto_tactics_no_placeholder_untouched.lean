import Mathlib

-- Assumptions: text is List Char. The successful rewrite is modelled on the split
-- the Rust performs — `head ++ marker ++ tail` — so `head` is everything before
-- `:= by` and `tail` the proof being discarded. `replaceAll` carries fuel rather
-- than a termination proof; the Rust's `str::replace` walks the string once.

def contains (needle hay : List Char) : Bool :=
  hay.tails.any (fun t => needle.isPrefixOf t)

def replaceAll (needle repl : List Char) : Nat → List Char → List Char
  | 0, s => s
  | _ + 1, [] => []
  | n + 1, c :: rest =>
      if needle.isPrefixOf (c :: rest) then
        repl ++ replaceAll needle repl n ((c :: rest).drop needle.length)
      else
        c :: replaceAll needle repl n rest

def rewrite (marker tactic head : List Char) : List Char :=
  head ++ marker ++ ' ' :: tactic ++ ['\n']

-- Nothing before the proof is touched: whatever tactic is written in, the
-- statement the caller submitted survives verbatim, so a rewrite cannot end up
-- proving something else.

theorem text_without_a_placeholder_is_untouched (needle repl : List Char) :
    ∀ (fuel : Nat) (s : List Char), contains needle s = false →
      replaceAll needle repl fuel s = s := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s hs
    cases s with
    | nil => rfl
    | cons c rest =>
      have hhead : needle.isPrefixOf (c :: rest) = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        have : contains needle (c :: rest) = true := by
          simp only [contains, List.any_eq_true]
          exact ⟨c :: rest, by simp [List.tails], hc⟩
        rw [this] at hs
        exact Bool.noConfusion hs
      have hrest : contains needle rest = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        simp only [contains, List.any_eq_true] at hc
        obtain ⟨t, ht, hp⟩ := hc
        have hbig : contains needle (c :: rest) = true := by
          simp only [contains, List.any_eq_true]
          refine ⟨t, ?_, hp⟩
          simp only [List.tails_cons, List.mem_cons]
          right
          exact ht
        rw [hbig] at hs
        exact Bool.noConfusion hs
      simp [replaceAll, hhead, ih rest hrest]
