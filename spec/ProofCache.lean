import Spec.Pystr

namespace ProofCache

/-- code: rust/formal-core/src/proof_cache.rs normalise_code -/
def normaliseCode (s : List Char) : List Char :=
  ['\n'].intercalate ((Pystr.splitlines (Pystr.strip s)).map Pystr.rstrip)

def normaliseCode.inputs : List (List Char) := Pystr.words 4

def replaceAllFor (pattern replacement : List Char) : Nat → List Char → List Char
  | 0, s => s
  | _ + 1, [] => []
  | fuel + 1, c :: rest =>
    if !pattern.isEmpty && pattern.isPrefixOf (c :: rest) then
      replacement ++ replaceAllFor pattern replacement fuel ((c :: rest).drop pattern.length)
    else c :: replaceAllFor pattern replacement fuel rest

def replaceAll (pattern replacement s : List Char) : List Char :=
  replaceAllFor pattern replacement s.length s

def asciiOperatorTable : List (List Char × List Char) :=
  [("<->", "↔"), ("->", "→"), ("/\\", "∧"), ("\\/", "∨"), ("<>", "≠"), ("<=", "≤"),
    (">=", "≥"), ("⟶", "→")].map fun (pattern, symbol) => (pattern.toList, symbol.toList)

def asciiOperators (s : List Char) : List Char :=
  asciiOperatorTable.foldl (fun text (pattern, symbol) => replaceAll pattern symbol text) s

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

def atBoundary : List Char → Bool
  | [] => true
  | c :: _ => !isWordChar c

def wordOperators (left : Bool) : List Char → List Char
  | 'f' :: 'o' :: 'r' :: 'a' :: 'l' :: 'l' :: rest =>
    if left && atBoundary rest then '∀' :: wordOperators true rest
    else 'f' :: wordOperators false ('o' :: 'r' :: 'a' :: 'l' :: 'l' :: rest)
  | 'e' :: 'x' :: 'i' :: 's' :: 't' :: 's' :: rest =>
    if left && atBoundary rest then '∃' :: wordOperators true rest
    else 'e' :: wordOperators false ('x' :: 'i' :: 's' :: 't' :: 's' :: rest)
  | 'n' :: 'o' :: 't' :: rest =>
    if left && atBoundary rest then '¬' :: wordOperators true rest
    else 'n' :: wordOperators false ('o' :: 't' :: rest)
  | 'i' :: 'n' :: rest =>
    if left && atBoundary rest then '∈' :: wordOperators true rest
    else 'i' :: wordOperators false ('n' :: rest)
  | c :: rest => c :: wordOperators (!isWordChar c) rest
  | [] => []

/-- code: rust/formal-core/src/proof_cache.rs normalise_formal -/
def normaliseFormal (s : List Char) : List Char :=
  (wordOperators true (asciiOperators s)).filter (fun c => !Pystr.isSpace c)

def operatorAlphabet : List Char := ['<', '-', '>', '=', '/', '\\', '⟶', 'i', 'n', 'a', ' ']

def normaliseFormal.inputs : List (List Char) :=
  Pystr.wordsOver operatorAlphabet 4 ++
    ["forall x, p x", "∀x", "forallx", "exists y", "not p", "a in b", "a_in_b", "x->y",
      "p <-> q", "p /\\ q", "p \\/ q", "a <> b", "a <= b", "a >= b", "a ⟶ b", "1in2",
      "(not)", "notin"].map String.toList

def frame (part : List Char) : List Char :=
  (Nat.repr part.length).toList ++ [':'] ++ part

def framed (parts : List (List Char)) : List Char :=
  (parts.map frame).flatten

def normaliseKind (kind : List Char) : List Char :=
  (Pystr.strip kind).map Char.toLower

def normalise_code_length_non_increasing : Prop :=
  ∀ s, (normaliseCode s).length ≤ s.length

def framed_shifting_a_boundary_changes_the_payload : Prop :=
  framed ["X\na".toList, ['b'], ['c']] ≠ framed [['X'], "a\nb".toList, ['c']]

def normalise_formal_word_operators_respect_boundaries : Prop :=
  normaliseFormal "a in b".toList = normaliseFormal "a∈b".toList ∧
    normaliseFormal "ainb".toList ≠ normaliseFormal "a∈b".toList

def cache_key_a_kind_differing_only_in_case_or_space_is_the_same_key : Prop :=
  normaliseKind "  Invariant ".toList = normaliseKind "invariant".toList

end ProofCache
