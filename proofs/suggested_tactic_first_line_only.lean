import Mathlib

-- Assumptions: text is List Char; splitlines modelled as splitting on '\n', which
-- is all the witnesses hold; trim modelled over spaces. `trim_matches('"')` takes
-- a set of characters, so it is dropWhile on both ends — which is the whole point
-- of the second witness.

def trimSpace (s : List Char) : List Char :=
  ((s.dropWhile (· = ' ')).reverse.dropWhile (· = ' ')).reverse

def trimQuotes (s : List Char) : List Char :=
  ((s.dropWhile (· = '"')).reverse.dropWhile (· = '"')).reverse

def suggested (s : List Char) : List Char :=
  trimSpace (trimQuotes (trimSpace ((s.splitOn '\n').headD [])))

theorem only_the_first_line_of_a_suggestion_is_taken :
    suggested "exact Nat.le_refl n\nexact foo".toList = "exact Nat.le_refl n".toList := by
  decide

-- The reason the Rust trims '"' and not "\n": trim_matches takes a set of
-- characters, so trimming "\n" would strip the trailing n from this very tactic.
-- Trimming quotes must leave it alone.
