import Mathlib

-- Assumptions: text is List Char; strip modelled over spaces, which is what the
-- witnesses hold; lowercasing is Char.toLower. A spec entry is modelled by the
-- field names it carries, and the id list by the ids validate collects in order.

def strip (s : List Char) : List Char :=
  ((s.dropWhile (· = ' ')).reverse.dropWhile (· = ' ')).reverse

def normKind (k : List Char) : List Char := (strip k).map Char.toLower

def duplicates (ids : List (List Char)) : List (List Char) :=
  ids.filter (fun id => 1 < ids.count id)

def missing (required present : List (List Char)) : List (List Char) :=
  required.filter (fun r => !present.contains r)

-- cache_key lowercases and strips the kind before framing it, so the same kind
-- written differently is the same key rather than a second cached proof.

theorem the_duplicate_check_is_exactly_nodup (ids : List (List Char)) :
    duplicates ids = [] ↔ ids.Nodup := by
  rw [duplicates, List.filter_eq_nil_iff, List.nodup_iff_count_le_one]
  constructor
  · intro h a
    by_cases ha : a ∈ ids
    · have := h a ha
      simp only [decide_eq_true_eq, Nat.not_lt] at this
      exact this
    · simp [List.count_eq_zero_of_not_mem ha]
  · intro h a ha
    have := h a
    simp only [decide_eq_true_eq, Nat.not_lt]
    exact this

-- A spec entry that is short a required field is refused rather than half-read,
-- and the refusal names every field that was missing — not just the first.
