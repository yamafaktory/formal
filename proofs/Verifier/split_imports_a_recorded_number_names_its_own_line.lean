import Mathlib

namespace Verifier

theorem in_range (isImport : List Char → Bool) :
    ∀ (lines : List (List Char)) (n number : Nat),
      number ∈ (split isImport lines n).2.2 → n ≤ number ∧ number < n + lines.length := by
  intro lines
  induction lines with
  | nil => intro n number hmem; simp [split] at hmem
  | cons line rest ih =>
    intro n number hmem
    rw [split] at hmem
    split_ifs at hmem with h
    · have := ih (n + 1) number hmem
      simp only [List.length_cons]
      omega
    · simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp only [List.length_cons]
        omega
      · have := ih (n + 1) number hmem
        simp only [List.length_cons]
        omega
theorem names_its_own_line (isImport : List Char → Bool) :
    ∀ (lines : List (List Char)) (n number : Nat) (line : List Char),
      (number, line) ∈ List.zip (split isImport lines n).2.2 (split isImport lines n).2.1 →
      lines[number - n]? = some line := by
  intro lines
  induction lines with
  | nil => intro n number line hmem; simp [split] at hmem
  | cons first rest ih =>
    intro n number line hmem
    rw [split] at hmem
    split_ifs at hmem with h
    · have hge := (in_range isImport rest (n + 1) number (List.of_mem_zip hmem).1).1
      have := ih (n + 1) number line hmem
      have hsub : number - n = (number - (n + 1)) + 1 := by omega
      rw [hsub]
      simpa using this
    · simp only [List.zip_cons_cons, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · rw [Prod.mk.injEq] at heq
        obtain ⟨h1, h2⟩ := heq
        subst h1
        subst h2
        simp
      · have hge := (in_range isImport rest (n + 1) number (List.of_mem_zip hmem).1).1
        have := ih (n + 1) number line hmem
        have hsub : number - n = (number - (n + 1)) + 1 := by omega
        rw [hsub]
        simpa using this

theorem split_imports_a_recorded_number_names_its_own_line.holds :
    split_imports_a_recorded_number_names_its_own_line :=
  fun isImport => names_its_own_line isImport

end Verifier
