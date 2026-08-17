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

theorem a_verdict_always_carries_its_reason (s : List Char) :
    (checkSyntax s).1 = true ↔ (checkSyntax s).2 = [] := by
  unfold checkSyntax
  split_ifs with h1 h2
  · simp only [emptyReason]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd h (by decide)
  · simp
  · simp only [keywordReason]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd h (by decide)

-- The pre-check tests for a substring, not a word, so a comment mentioning
-- "important" satisfies the requirement for "import" and the file is passed to
-- Lean. Cheap to accept and expensive to reject wrongly, so this is the safe
-- direction for a pre-check — but check_syntax also gates can_cache.
