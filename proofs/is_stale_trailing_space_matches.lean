import Mathlib

-- Assumptions: text is List Char; splitlines is modelled as splitting on '\n',
-- which is all these witnesses contain; normalise_code is strip-then-rstrip-each-line,
-- as in the Rust. The staleness test is Rust's `contains`, modelled as an infix
-- search over the suffixes.

def isSpace (c : Char) : Bool := c = ' '

def rstrip (s : List Char) : List Char := (s.reverse.dropWhile isSpace).reverse

def strip (s : List Char) : List Char := rstrip (s.dropWhile isSpace)

def normalise (s : List Char) : List Char :=
  List.intercalate ['\n'] (((strip s).splitOn '\n').map rstrip)

def contains (needle haystack : List Char) : Bool :=
  haystack.tails.any (fun t => needle.isPrefixOf t)

def describes (current recorded : List Char) : Bool :=
  contains (normalise recorded) (normalise current)

-- The witnesses: one function, the same function with trailing space on each line,
-- and the same function indented one level deeper.
def recorded : List Char := "def f():\n    return 1".toList

def withTrailingSpace : List Char := "def f():   \n    return 1   ".toList

def reindented : List Char := "    def f():\n        return 1".toList

theorem trailing_space_does_not_break_the_match :
    describes withTrailingSpace recorded = true := by
  decide

-- The counterexample. normalise_code rstrips each line but preserves indentation —
-- "indentation is meaning" — so moving a function one level deeper does change it,
-- and the property is reported stale.
