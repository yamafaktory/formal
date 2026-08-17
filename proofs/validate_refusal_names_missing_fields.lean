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

theorem the_refusal_names_every_missing_field
    (required present : List (List Char)) (r : List Char) :
    r ∈ missing required present ↔ (r ∈ required ∧ r ∉ present) := by
  simp [missing, List.mem_filter]
