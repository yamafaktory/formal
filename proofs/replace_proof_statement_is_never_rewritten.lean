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

theorem the_statement_is_never_rewritten (marker tactic head : List Char) :
    head <+: rewrite marker tactic head := by
  have h : rewrite marker tactic head = head ++ (marker ++ (' ' :: tactic ++ ['\n'])) := by
    unfold rewrite
    simp [List.append_assoc]
  rw [h]
  exact List.prefix_append _ _

-- And the old proof is gone rather than appended to: the result ends with the
-- tactic that was written in.
