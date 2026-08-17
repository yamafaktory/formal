import Mathlib

def inSeparatorRange (c : Char) : Bool :=
  0x1c ≤ c.toNat && c.toNat ≤ 0x1f

def isSpace (ws : Char → Bool) (c : Char) : Bool :=
  ws c || inSeparatorRange c

-- Assumptions: the Unicode whitespace predicate `char::is_whitespace` is left
-- abstract as `ws`, so the claim holds whatever Unicode says; the inclusive char
-- range '\u{1c}'..='\u{1f}' is modelled as a comparison on code points.

theorem separator_range_closed_at_both_ends (ws : Char → Bool) :
    isSpace ws '\x1c' = true ∧ isSpace ws '\x1f' = true ∧
      isSpace ws '\x1b' = ws '\x1b' ∧ isSpace ws ' ' = ws ' ' := by
  have h1 : inSeparatorRange '\x1c' = true := by decide
  have h2 : inSeparatorRange '\x1f' = true := by decide
  have h3 : inSeparatorRange '\x1b' = false := by decide
  have h4 : inSeparatorRange ' ' = false := by decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [isSpace, h1, h2, h3, h4]
