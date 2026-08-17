import Mathlib

-- Assumptions: text is List Char. `contains` is Rust's substring `contains`,
-- modelled as an infix search over the suffixes; blankness is the trim the Rust
-- performs, modelled over spaces and newlines, which is what the witnesses hold.

def contains (needle hay : List Char) : Bool :=
  hay.tails.any (fun t => needle.isPrefixOf t)

def keywords : List (List Char) :=
  ["import", "theorem", "lemma", "def", "example"].map String.toList

def blank (s : List Char) : Bool :=
  (s.filter (fun c => !(c = ' ' || c = '\n'))).isEmpty

def emptyReason : List Char := "Empty Lean code".toList

def keywordReason : List Char :=
  "Code must contain at least one of: import, theorem, lemma, def, example".toList

def checkSyntax (s : List Char) : Bool × List Char :=
  if blank s then (false, emptyReason)
  else if keywords.any (fun k => contains k s) then (true, [])
  else (false, keywordReason)

theorem a_word_that_merely_contains_a_keyword_is_accepted :
    (checkSyntax "-- important note".toList).1 = true := by
  decide
