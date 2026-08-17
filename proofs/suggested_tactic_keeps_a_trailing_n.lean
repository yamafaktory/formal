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

theorem trimming_quotes_does_not_eat_a_trailing_n :
    suggested "\"exact Nat.le_refl n\"".toList = "exact Nat.le_refl n".toList := by
  decide
