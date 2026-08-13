import Mathlib

-- Assumptions: text modelled as List Char; the decimal length prefix is Nat.repr,
-- matching Python's f"{len(part)}:{part}".

def framedOne (p : List Char) : List Char :=
  (Nat.repr p.length).toList ++ [':'] ++ p

def framed (parts : List (List Char)) : List Char :=
  (parts.map framedOne).flatten

-- The witness that collided when the payload was joined on a newline: two distinct
-- field tuples whose newline-join is identical.
theorem framed_distinguishes_shifted_boundary :
    framed [['X', '\n', 'a'], ['b'], ['c']] ≠ framed [['X'], ['a', '\n', 'b'], ['c']] := by
  decide
