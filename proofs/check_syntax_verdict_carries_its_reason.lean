import Mathlib

-- Assumptions: text is List Char. `contains` is Rust's substring `contains`,
-- modelled as an infix search over the suffixes; blankness is the trim the Rust
-- performs, modelled over spaces and newlines, which is what the witnesses hold.
-- `runs_code` is left abstract as `screen`, which returns the construct it found.
-- The empty and the runs-code refusals are cut to their opening words. formal's screen
-- refuses `Lean`, `IO` and `#eval` even inside a string, and the claim needs only a
-- nonempty reason.

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

theorem a_verdict_always_carries_its_reason (screen : List Char → Option (List Char))
    (s : List Char) : (checkSyntax screen s).1 = true ↔ (checkSyntax screen s).2 = [] := by
  have runs : ∀ found, runsReason found ≠ [] := fun _ =>
    List.append_ne_nil_of_left_ne_nil (by decide) _
  have empty : emptyReason ≠ [] := by decide
  have keyword : keywordReason ≠ [] := by decide
  unfold checkSyntax
  split_ifs <;> rcases screen s with _ | found <;> simp [runs, empty, keyword]

-- The pre-check tests for a substring, not a word, so a comment mentioning
-- "important" satisfies the requirement for "import" and the file is passed to
-- Lean. Cheap to accept and expensive to reject wrongly, so this is the safe
-- direction for a pre-check — but check_syntax also gates can_cache.
