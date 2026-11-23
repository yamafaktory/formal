namespace Pystr

def alphabet : List Char :=
  ['a', ' ', '\t', '\u00a0', '\x1f', '\n', '\x0b', '\x0c', '\x1c', '\x1d', '\x1e', '\r', '\x85',
    '\u2028', '\u2029']

def Char.samples : List Char := alphabet

def sentences (fragments : List (List Char)) : Nat → List (List Char)
  | 0 => [[]]
  | n + 1 => [] :: fragments.flatMap fun fragment => (sentences fragments n).map (fragment ++ ·)

def wordsOver (letters : List Char) (n : Nat) : List (List Char) :=
  sentences (letters.map ([·])) n

def words (n : Nat) : List (List Char) := wordsOver alphabet n

/-- code: rust/formal-core/src/pystr.rs is_space -/
def isSpace (c : Char) : Bool :=
  [0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x1c, 0x1d, 0x1e, 0x1f, 0x20, 0x85, 0xa0, 0x1680,
    0x2028, 0x2029, 0x202f, 0x205f, 0x3000].contains c.toNat ||
    (0x2000 ≤ c.toNat && c.toNat ≤ 0x200a)

def isSpace.inputs : List Char :=
  ((List.range 0x110000).filter Nat.isValidChar).map Char.ofNat

def isBreak (c : Char) : Bool :=
  [0x0a, 0x0b, 0x0c, 0x0d, 0x1c, 0x1d, 0x1e, 0x85, 0x2028, 0x2029].contains c.toNat

/-- code: rust/formal-core/src/pystr.rs rstrip -/
def rstrip (s : List Char) : List Char :=
  (s.reverse.dropWhile isSpace).reverse

def rstrip.inputs : List (List Char) := words 4

/-- code: rust/formal-core/src/pystr.rs strip -/
def strip (s : List Char) : List Char :=
  rstrip (s.dropWhile isSpace)

def strip.inputs : List (List Char) := words 4

def splitlines.go (line : List Char) : List Char → List (List Char)
  | [] => if line.isEmpty then [] else [line]
  | '\r' :: '\n' :: rest => line :: go [] rest
  | c :: rest => if isBreak c then line :: go [] rest else go (line ++ [c]) rest

/-- code: rust/formal-core/src/pystr.rs splitlines -/
def splitlines (s : List Char) : List (List Char) :=
  splitlines.go [] s

def splitlines.inputs : List (List Char) := words 4

def is_space_the_separator_control_range_is_space : Prop :=
  ∀ c : Char, 0x1c ≤ c.toNat → c.toNat ≤ 0x1f → isSpace c = true

def rstrip_removes_only_a_suffix_of_space : Prop :=
  ∀ s, ∃ z, s = rstrip s ++ z ∧ ∀ c ∈ z, isSpace c = true

def rstrip_never_ends_in_space : Prop :=
  ∀ s t c, rstrip s = t ++ [c] → isSpace c = false

def rstrip_idempotent : Prop :=
  ∀ s, rstrip (rstrip s) = rstrip s

def strip_removes_a_prefix_and_a_suffix_of_space : Prop :=
  ∀ s, ∃ pre suf, s = pre ++ strip s ++ suf ∧
    (∀ c ∈ pre, isSpace c = true) ∧ (∀ c ∈ suf, isSpace c = true)

def strip_ends_are_not_space : Prop :=
  ∀ s, (∀ c t, strip s = c :: t → isSpace c = false) ∧
    (∀ t c, strip s = t ++ [c] → isSpace c = false)

def strip_idempotent : Prop :=
  ∀ s, strip (strip s) = strip s

def splitlines_a_break_ends_the_line_before_it : Prop :=
  ∀ a, (∀ c ∈ a, isBreak c = false) →
    ∀ br, isBreak br = true → br ≠ '\r' → ∀ b, splitlines (a ++ br :: b) = a :: splitlines b

def splitlines_crlf_is_one_boundary : Prop :=
  ∀ a, (∀ c ∈ a, isBreak c = false) →
    ∀ b, splitlines (a ++ '\r' :: '\n' :: b) = a :: splitlines b

def splitlines_a_bare_cr_is_a_boundary : Prop :=
  ∀ a, (∀ c ∈ a, isBreak c = false) →
    ∀ b, (∀ t, b ≠ '\n' :: t) → splitlines (a ++ '\r' :: b) = a :: splitlines b

def splitlines_no_line_contains_a_break : Prop :=
  ∀ s, ∀ l ∈ splitlines s, ∀ c ∈ l, isBreak c = false

def splitlines_text_without_a_break_is_one_line : Prop :=
  ∀ s, (∀ c ∈ s, isBreak c = false) → splitlines s = if s = [] then [] else [s]

end Pystr
