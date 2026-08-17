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

theorem every_promoted_sorry_is_reported_as_an_error
    (hasSorry : List Char → Bool) (ms : List Msg) (m : Msg)
    (h : m ∈ promoted hasSorry ms) : m.severity = errorSeverity := by
  simp only [promoted, List.mem_map] at h
  obtain ⟨x, _, hx⟩ := h
  rw [← hx]
  rfl
