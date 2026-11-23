import Mathlib

-- Assumptions: text is List Char. `contains` is Rust's substring `contains`,
-- modelled as an infix search over the suffixes; blankness is the trim the Rust
-- performs, modelled over spaces and newlines, which is what the witnesses hold.
-- `runs_code` is left abstract as `screen`, which returns the construct it found.
-- The empty and the runs-code refusals are cut to their opening words. formal's screen
-- refuses `Lean`, `IO` and `#eval` even inside a string, and the claim needs only a
-- nonempty reason.
-- It ignores comments, so it finds nothing in the witness, which is a comment.

def contains (needle hay : List Char) : Bool :=
  hay.tails.any (fun t => needle.isPrefixOf t)

def keywords : List (List Char) :=
  ["import", "theorem", "lemma", "def", "example"].map String.toList

def blank (s : List Char) : Bool :=
  (s.filter (fun c => !(c = ' ' || c = '\n'))).isEmpty

def emptyReason : List Char := "Empty".toList

def keywordReason : List Char :=
  "Code must contain at least one of: import, theorem, lemma, def, example".toList

def runsReason (found : List Char) : List Char :=
  "The proof contains `".toList ++ found

def checkSyntax (screen : List Char → Option (List Char)) (s : List Char) : Bool × List Char :=
  if blank s then (false, emptyReason)
  else match screen s with
    | some found => (false, runsReason found)
    | none =>
      if keywords.any (fun k => contains k s) then (true, [])
      else (false, keywordReason)

theorem a_word_that_merely_contains_a_keyword_is_accepted
    (screen : List Char → Option (List Char)) (h : screen "-- important note".toList = none) :
    (checkSyntax screen "-- important note".toList).1 = true := by
  simp only [checkSyntax, h]
  decide
