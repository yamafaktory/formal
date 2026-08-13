import Mathlib

-- Assumptions: text modelled as List Char. Only the membership operator is modelled,
-- which is all these witnesses exercise; a word is replaced only when neither
-- neighbour is a word character, matching the \b...\b in the Python.

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

def isSpaceC (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def replaceIn : Bool → List Char → List Char
  | leftBoundary, 'i' :: 'n' :: rest =>
      let rightBoundary := match rest with
        | [] => true
        | c :: _ => !isWordChar c
      if leftBoundary && rightBoundary then '∈' :: replaceIn true rest
      else 'i' :: replaceIn false ('n' :: rest)
  | _, c :: rest => c :: replaceIn (!isWordChar c) rest
  | _, [] => []

def normaliseFormal (l : List Char) : List Char :=
  (replaceIn true l).filter (fun c => !isSpaceC c)

-- The spelled operator and the symbol reach one normal form ...
theorem in_word_and_symbol_agree :
    normaliseFormal ['a', ' ', 'i', 'n', ' ', 'b'] = normaliseFormal ['a', '∈', 'b'] := by
  decide

-- ... while an identifier that merely contains those letters does not. This is the
-- collision that put two unrelated properties under one cache key.
theorem identifier_is_not_the_operator :
    normaliseFormal ['a', 'i', 'n', 'b'] ≠ normaliseFormal ['a', '∈', 'b'] := by
  decide
