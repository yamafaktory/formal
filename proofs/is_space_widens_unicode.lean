import Mathlib

def inSeparatorRange (c : Char) : Bool :=
  0x1c ≤ c.toNat && c.toNat ≤ 0x1f

def isSpace (ws : Char → Bool) (c : Char) : Bool :=
  ws c || inSeparatorRange c

-- Assumptions: the Unicode whitespace predicate `char::is_whitespace` is left
-- abstract as `ws`; U+001C is not Unicode White_Space, which enters as the
-- hypothesis `ws '\x1c' = false` rather than as a fact about the model.

theorem widens_unicode_whitespace (ws : Char → Bool) (h : ws '\x1c' = false) :
    isSpace ws '\x1c' ≠ ws '\x1c' := by
  have h1 : inSeparatorRange '\x1c' = true := by decide
  simp [isSpace, h, h1]
