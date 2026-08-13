import Mathlib

-- Assumptions: text modelled as List Char; splitlines modelled as splitting on '\n';
-- strip and rstrip remove whitespace only. Joining is List.intercalate ['\n'], whose
-- round trip with splitOn is List.intercalate_splitOn.

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def rstrip (l : List Char) : List Char := (l.reverse.dropWhile isSpace).reverse

def strip (l : List Char) : List Char := rstrip (l.dropWhile isSpace)

def normaliseCode (l : List Char) : List Char :=
  ['\n'].intercalate (((strip l).splitOn '\n').map rstrip)

theorem rstrip_length_le (l : List Char) : (rstrip l).length ≤ l.length := by
  simp only [rstrip, List.length_reverse]
  exact le_trans (List.length_dropWhile_le _ _) (by simp)

theorem strip_length_le (l : List Char) : (strip l).length ≤ l.length :=
  le_trans (rstrip_length_le _) (List.length_dropWhile_le _ _)

theorem intercalate_map_rstrip_le (ls : List (List Char)) :
    (['\n'].intercalate (ls.map rstrip)).length ≤ (['\n'].intercalate ls).length := by
  induction ls with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simpa [List.intercalate] using rstrip_length_le a
    | cons b u =>
      simp only [List.intercalate, List.map_cons, List.intersperse_cons₂, List.flatten_cons,
        List.length_append] at ih ⊢
      have := rstrip_length_le a
      omega

theorem normalise_code_length_non_increasing (l : List Char) :
    (normaliseCode l).length ≤ l.length := by
  have h := intercalate_map_rstrip_le ((strip l).splitOn '\n')
  rw [List.intercalate_splitOn] at h
  exact le_trans h (strip_length_le l)
