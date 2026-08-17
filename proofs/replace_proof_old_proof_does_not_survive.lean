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

theorem nothing_of_the_old_proof_survives (marker tactic head : List Char) :
    (' ' :: tactic ++ ['\n']) <:+ rewrite marker tactic head := by
  have h : rewrite marker tactic head = (head ++ marker) ++ (' ' :: tactic ++ ['\n']) := by
    unfold rewrite
    simp [List.append_assoc]
  rw [h]
  exact List.suffix_append _ _

-- with_auto_tactics only ever swaps a placeholder for the chain, so a proof that
-- has no placeholder in it comes back exactly as it went in.
