import Mathlib

-- Assumptions: a Lean diagnostic is its severity and its data, both List Char.
-- The two substring tests parse_output performs — "declaration uses 'sorry'" on an
-- error, and "sorry" on a warning — are left abstract as `isSorryDecl` and
-- `hasSorry`, so the claims hold whatever those spellings are.

structure Msg where
  severity : List Char
  data : List Char
deriving DecidableEq

def errorSeverity : List Char := "error".toList

def warningSeverity : List Char := "warning".toList

def promote (m : Msg) : Msg := { m with severity := errorSeverity }

def realErrors (isSorryDecl : List Char → Bool) (ms : List Msg) : List Msg :=
  ms.filter (fun m => decide (m.severity = errorSeverity) && !isSorryDecl m.data)

def promoted (hasSorry : List Char → Bool) (ms : List Msg) : List Msg :=
  (ms.filter (fun m => decide (m.severity = warningSeverity) && hasSorry m.data)).map promote

def collect (isSorryDecl hasSorry : List Char → Bool) (ms : List Msg) : List Msg :=
  realErrors isSorryDecl ms ++ promoted hasSorry ms

def success (code : Option Nat) (errors : List Msg) : Bool :=
  decide (code = some 0) && errors.isEmpty

theorem a_sorry_warning_is_never_a_success
    (isSorryDecl hasSorry : List Char → Bool) (ms : List Msg) (code : Option Nat)
    (m : Msg) (hmem : m ∈ ms) (hw : m.severity = warningSeverity)
    (hs : hasSorry m.data = true) :
    success code (collect isSorryDecl hasSorry ms) = false := by
  have hin : promote m ∈ promoted hasSorry ms := by
    simp only [promoted, List.mem_map]
    exact ⟨m, by simp [List.mem_filter, hmem, hw, hs], rfl⟩
  have hne : collect isSorryDecl hasSorry ms ≠ [] := by
    intro h
    have : promoted hasSorry ms = [] := by
      simp only [collect, List.append_eq_nil_iff] at h
      exact h.2
    rw [this] at hin
    simp at hin
  simp only [success, Bool.and_eq_false_iff, List.isEmpty_eq_false_iff_exists_mem]
  right
  rcases List.exists_mem_of_ne_nil _ hne with ⟨x, hx⟩
  exact ⟨x, hx⟩
