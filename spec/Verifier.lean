import Spec.ProofCache

namespace Verifier

/-- code: core char::is_whitespace -/
def isWhitespace (c : Char) : Bool :=
  Pystr.isSpace c && !(0x1c ≤ c.toNat && c.toNat ≤ 0x1f)

def isWhitespace.inputs : List Char := Pystr.isSpace.inputs

def trimBy (drop : Char → Bool) (s : List Char) : List Char :=
  ((s.dropWhile drop).reverse.dropWhile drop).reverse

def trim (s : List Char) : List Char := trimBy isWhitespace s

def split (isImport : List Char → Bool) :
    List (List Char) → Nat → List (List Char) × List (List Char) × List Nat
  | [], _ => ([], [], [])
  | line :: rest, n =>
    if isImport line then
      (line :: (split isImport rest (n + 1)).1, (split isImport rest (n + 1)).2.1,
        (split isImport rest (n + 1)).2.2)
    else
      ((split isImport rest (n + 1)).1, line :: (split isImport rest (n + 1)).2.1,
        n :: (split isImport rest (n + 1)).2.2)

def firstLine (before : Nat) : Nat := before + 2

def lastLine (before body : Nat) : Nat := before + 1 + body

def covers (first last line : Nat) : Prop := first ≤ line ∧ line ≤ last

def spans : List Nat → Nat → List (Nat × Nat)
  | [], _ => []
  | body :: rest, before => (firstLine before, lastLine before body) :: spans rest (before + body + 3)

def keywords : List (List Char) :=
  ["import", "theorem", "lemma", "def", "example"].map String.toList

def emptyReason : List Char := "Empty".toList

def runsReason (found : List Char) : List Char := "The proof contains `".toList ++ found

def keywordReason : List Char :=
  "Code must contain at least one of: import, theorem, lemma, def, example".toList

def checkSyntax (screen : List Char → Option (List Char)) (s : List Char) : Bool × List Char :=
  if s.all isWhitespace then (false, emptyReason)
  else
    match screen s with
    | some found => (false, runsReason found)
    | none =>
      if keywords.any fun keyword => decide (keyword <:+: s) then (true, [])
      else (false, keywordReason)

def marker : List Char := ":= by".toList

def countFor (pattern : List Char) : Nat → List Char → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | fuel + 1, c :: rest =>
    if pattern.isPrefixOf (c :: rest) then
      1 + countFor pattern fuel ((c :: rest).drop pattern.length)
    else countFor pattern fuel rest

def splitOnce (pattern : List Char) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if pattern.isPrefixOf (c :: rest) then ([], (c :: rest).drop pattern.length)
    else ((c :: (splitOnce pattern rest).1), (splitOnce pattern rest).2)

def declarationKeywords : List (List Char) :=
  ["theorem", "lemma", "def", "example", "instance", "abbrev"].map String.toList

def declaresAtLineStart (s : List Char) : Bool :=
  declarationKeywords.any fun keyword =>
    keyword.isPrefixOf (s.dropWhile isWhitespace) &&
      ProofCache.atBoundary ((s.dropWhile isWhitespace).drop keyword.length)

def declaresAfterABreak : List Char → Bool
  | [] => false
  | c :: rest => (c == '\n' && declaresAtLineStart rest) || declaresAfterABreak rest

def declares (s : List Char) : Bool :=
  declaresAtLineStart s || declaresAfterABreak s

def replaceProof (code tactic : List Char) : Option (List Char) :=
  if countFor marker code.length code != 1 then none
  else if declares (splitOnce marker code).2 then none
  else some ((splitOnce marker code).1 ++ marker ++ ' ' :: tactic ++ ['\n'])

/-- code: rust/formal-lean/src/verifier.rs replace_proof -/
def replaceProofOn (input : List Char × List Char) : Option (List Char) :=
  replaceProof input.1 input.2

def replaceProofOn.inputs : List (List Char × List Char) :=
  (Pystr.sentences (["theorem t ", ":= by", " simp", "\n", "def", "lemma x", " ", "α", "　", "\r",
    "abbrev_"].map String.toList) 4).map (·, "rfl".toList)

def autoTactics : List Char :=
  ("first | " ++ " | ".intercalate
    (["rfl", "omega", "norm_num", "linarith", "ring", "decide", "simp"].map
      fun step => "(" ++ step ++ "; done)")).toList

/-- code: rust/formal-lean/src/verifier.rs with_auto_tactics -/
def withAutoTactics (s : List Char) : List Char :=
  ProofCache.replaceAll "by\n  sorry".toList ("by ".toList ++ autoTactics)
    (ProofCache.replaceAll ":= by sorry".toList (":= by ".toList ++ autoTactics) s)

def withAutoTactics.inputs : List (List Char) :=
  Pystr.sentences ([":= by sorry", "by\n  sorry", ":= by", " sorry", "by", "\n", "  ", "x"].map
    String.toList) 4

def trimQuotes (s : List Char) : List Char := trimBy (· == '"') s

def tacticOf (captured : List Char) : List Char :=
  trim (trimQuotes (trim ((Pystr.splitlines captured).headD [])))

def split_imports_conservation : Prop :=
  ∀ isImport lines n,
    (split isImport lines n).1.length + (split isImport lines n).2.1.length = lines.length

def split_imports_every_body_line_is_numbered : Prop :=
  ∀ isImport lines n, (split isImport lines n).2.1.length = (split isImport lines n).2.2.length

def split_imports_a_recorded_number_is_in_range : Prop :=
  ∀ isImport lines n number, number ∈ (split isImport lines n).2.2 →
    n ≤ number ∧ number < n + lines.length

def split_imports_a_recorded_number_names_its_own_line : Prop :=
  ∀ isImport lines n number line,
    (number, line) ∈ List.zip (split isImport lines n).2.2 (split isImport lines n).2.1 →
    lines[number - n]? = some line

def build_batch_an_entry_spans_exactly_its_body : Prop :=
  ∀ before body, 0 < body → lastLine before body + 1 - firstLine before = body

def build_batch_an_empty_body_spans_nothing : Prop :=
  ∀ before line, ¬ covers (firstLine before) (lastLine before 0) line

def build_batch_the_span_holds_the_body : Prop :=
  ∀ (before : List (List Char)) namespaceLine endLine (body : List (List Char)) j,
    j < body.length →
    (before ++ namespaceLine :: (body ++ [endLine]))[firstLine before.length + j - 1]? = body[j]?

def build_batch_every_span_starts_after_where_it_was_laid_out : Prop :=
  ∀ bodies before span, span ∈ spans bodies before → before + 2 ≤ span.1

def rebase_an_error_inside_an_entry_always_rebases : Prop :=
  ∀ before body line, covers (firstLine before) (lastLine before body) line →
    line - firstLine before < body

def verify_batch_no_line_is_claimed_by_two_entries : Prop :=
  ∀ bodies before body line span, span ∈ spans bodies (before + body + 3) →
    covers (firstLine before) (lastLine before body) line → ¬ covers span.1 span.2 line

def check_syntax_a_verdict_always_carries_its_reason : Prop :=
  ∀ screen s, (checkSyntax screen s).1 = true ↔ (checkSyntax screen s).2 = []

def check_syntax_a_word_that_merely_contains_a_keyword_is_accepted : Prop :=
  ∀ screen, screen "-- important note".toList = none →
    (checkSyntax screen "-- important note".toList).1 = true

def replace_proof_the_statement_is_never_rewritten : Prop :=
  ∀ code tactic result, replaceProof code tactic = some result →
    (splitOnce marker code).1 <+: result

def replace_proof_nothing_of_the_old_proof_survives : Prop :=
  ∀ code tactic result, replaceProof code tactic = some result →
    marker ++ ' ' :: tactic ++ ['\n'] <:+ result

def with_auto_tactics_text_without_a_placeholder_is_untouched : Prop :=
  ∀ s, ¬ ":= by sorry".toList <:+: s → ¬ "by\n  sorry".toList <:+: s → withAutoTactics s = s

def suggested_tactic_only_the_first_line_of_a_suggestion_is_taken : Prop :=
  tacticOf "exact Nat.le_refl n\u2028exact foo".toList = "exact Nat.le_refl n".toList

def suggested_tactic_trimming_quotes_does_not_eat_a_trailing_n : Prop :=
  tacticOf "\"exact Nat.le_refl n\"".toList = "exact Nat.le_refl n".toList

end Verifier
