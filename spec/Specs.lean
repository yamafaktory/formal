import Spec.ProofCache

namespace Specs

def describes (current recorded : List Char) : Bool :=
  decide (ProofCache.normaliseCode recorded <:+: ProofCache.normaliseCode current)

def duplicates (ids : List (List Char)) : List (List Char) :=
  ids.filter fun id => 1 < ids.count id

def missing (required present : List (List Char)) : List (List Char) :=
  required.filter fun field => !present.contains field

def is_stale_trailing_space_does_not_break_the_match : Prop :=
  describes "def f():   \n    return 1   ".toList "def f():\n    return 1".toList = true

def is_stale_reindenting_does_break_the_match : Prop :=
  describes "    def f():\n        return 1".toList "def f():\n    return 1".toList = false

def validate_the_duplicate_check_is_exactly_nodup : Prop :=
  ∀ ids, duplicates ids = [] ↔ ids.Nodup

def validate_the_refusal_names_every_missing_field : Prop :=
  ∀ required present field, field ∈ missing required present ↔ (field ∈ required ∧ field ∉ present)

end Specs
