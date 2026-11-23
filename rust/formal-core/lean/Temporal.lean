namespace Temporal

def states {σ α : Type} (init : σ) (step : σ → α → σ) (run : Nat → α) : Nat → σ
  | 0 => init
  | n + 1 => step (states init step run n) (run n)

inductive Reachable {σ α : Type} (init : σ) (step : σ → α → σ) : σ → Prop
  | start : Reachable init step init
  | next {s : σ} (a : α) : Reachable init step s → Reachable init step (step s a)

def fair {α : Type} (a : α) (run : Nat → α) : Prop :=
  ∀ n, ∃ m, n ≤ m ∧ run m = a

def always {σ α : Type} (init : σ) (step : σ → α → σ) (p : σ → Prop) : Prop :=
  ∀ s, Reachable init step s → p s

def eventually {σ α : Type} (init : σ) (step : σ → α → σ) (assumed : (Nat → α) → Prop)
    (p : σ → Prop) : Prop :=
  (∃ run, assumed run) ∧ ∀ run, assumed run → ∃ n, p (states init step run n)

def leadsTo {σ α : Type} (init : σ) (step : σ → α → σ) (assumed : (Nat → α) → Prop)
    (p q : σ → Prop) : Prop :=
  (∃ run, assumed run) ∧ ∀ run, assumed run → ∀ n, p (states init step run n) →
    ∃ m, n ≤ m ∧ q (states init step run m)

theorem reachable_states {σ α : Type} {init : σ} {step : σ → α → σ} (run : Nat → α) (n : Nat) :
    Reachable init step (states init step run n) := by
  induction n with
  | zero => exact .start
  | succ n ih => exact .next _ ih

theorem fair_constant {α : Type} (a : α) : fair a (fun _ => a) :=
  fun n => ⟨n, Nat.le_refl n, rfl⟩

def cycle {α : Type} (first : α) (rest : List α) (n : Nat) : α :=
  (first :: rest).getD (n % (rest.length + 1)) first

theorem fair_cycle {α : Type} (first : α) (rest : List α) (a : α) (listed : a ∈ first :: rest) :
    fair a (cycle first rest) := by
  obtain ⟨i, hi, found⟩ := List.getElem_of_mem listed
  simp only [List.length_cons] at hi
  intro n
  refine ⟨n * (rest.length + 1) + i, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_right n (show 0 < rest.length + 1 by omega)
    omega
  · show (first :: rest).getD ((n * (rest.length + 1) + i) % (rest.length + 1)) first = a
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
    simp only [List.getD, List.getElem?_eq_getElem (show i < (first :: rest).length by simp; omega), found,
      Option.getD_some]

theorem always_true {σ α : Type} {init : σ} {step : σ → α → σ} :
    always init step (fun _ => True) :=
  fun _ _ => trivial

theorem always_of_inductive {σ α : Type} {init : σ} {step : σ → α → σ} {p : σ → Prop}
    (starts : p init) (kept : ∀ s a, p s → p (step s a)) : always init step p := by
  intro s reached
  induction reached with
  | start => exact starts
  | next a _ ih => exact kept _ a ih

theorem leadsTo_of_measure {σ α : Type} {init : σ} {step : σ → α → σ} {p q inv : σ → Prop}
    {assumed : (Nat → α) → Prop} (a : α) (fairness : ∀ run, assumed run → fair a run)
    (possible : ∃ run, assumed run) (invariant : always init step inv) (μ : σ → Nat)
    (kept : ∀ s b, inv s → p s → ¬ q s → q (step s b) ∨ (p (step s b) ∧ μ (step s b) ≤ μ s))
    (helps : ∀ s, inv s → p s → ¬ q s → q (step s a) ∨ (p (step s a) ∧ μ (step s a) < μ s)) :
    leadsTo init step assumed p q := by
  refine ⟨possible, ?_⟩
  intro run hr n start
  have holds : ∀ j, inv (states init step run j) := fun j => invariant _ (reachable_states run j)
  apply Classical.byContradiction
  intro none
  have noq : ∀ m, n ≤ m → ¬ q (states init step run m) := fun m hm hq => none ⟨m, hm, hq⟩
  have next : ∀ j, n ≤ j → p (states init step run j) →
      p (states init step run (j + 1)) ∧
        μ (states init step run (j + 1)) ≤ μ (states init step run j) := by
    intro j hj hp
    rcases kept _ (run j) (holds j) hp (noq j hj) with h | h
    · exact absurd h (noq (j + 1) (by omega))
    · exact h
  have stay : ∀ d, p (states init step run (n + d)) := by
    intro d
    induction d with
    | zero => exact start
    | succ d ih => exact (next (n + d) (by omega) ih).1
  have mono : ∀ j e, n ≤ j → μ (states init step run (j + e)) ≤ μ (states init step run j) := by
    intro j e hj
    induction e with
    | zero => exact Nat.le_refl _
    | succ e ih =>
      have hp : p (states init step run (j + e)) := by
        have := stay (j + e - n); rwa [show n + (j + e - n) = j + e by omega] at this
      exact Nat.le_trans (next (j + e) (by omega) hp).2 ih
  have drop : ∀ k, ∃ j, n ≤ j ∧ μ (states init step run j) + k ≤ μ (states init step run n) := by
    intro k
    induction k with
    | zero => exact ⟨n, Nat.le_refl _, by omega⟩
    | succ k ih =>
      obtain ⟨j, hj, hd⟩ := ih
      obtain ⟨m, hm, ha⟩ := fairness run hr j
      have hp : p (states init step run m) := by
        have := stay (m - n); rwa [show n + (m - n) = m by omega] at this
      have hmj := mono j (m - j) hj
      rw [show j + (m - j) = m by omega] at hmj
      have h := helps _ (holds m) hp (noq m (by omega))
      rw [← ha] at h
      rcases h with h | ⟨_, hlt⟩
      · exact absurd h (noq (m + 1) (by omega))
      · exact ⟨m + 1, by omega, by
          show μ (step (states init step run m) (run m)) + (k + 1) ≤ _
          omega⟩
  obtain ⟨j, _, hd⟩ := drop (μ (states init step run n) + 1)
  omega

theorem leadsTo_of_fair_step {σ α : Type} {init : σ} {step : σ → α → σ} {p q inv : σ → Prop}
    {assumed : (Nat → α) → Prop} (a : α) (fairness : ∀ run, assumed run → fair a run)
    (possible : ∃ run, assumed run) (invariant : always init step inv)
    (kept : ∀ s b, inv s → p s → ¬ q s → p (step s b) ∨ q (step s b))
    (helps : ∀ s, inv s → p s → ¬ q s → q (step s a)) :
    leadsTo init step assumed p q :=
  leadsTo_of_measure a fairness possible invariant (fun _ => 0)
    (fun s b hi hp hq => (kept s b hi hp hq).elim (fun h => Or.inr ⟨h, Nat.le_refl _⟩) Or.inl)
    (fun s hi hp hq => Or.inl (helps s hi hp hq))

theorem leadsTo_trans {σ α : Type} {init : σ} {step : σ → α → σ} {assumed : (Nat → α) → Prop}
    {p q r : σ → Prop} (first : leadsTo init step assumed p q)
    (second : leadsTo init step assumed q r) : leadsTo init step assumed p r := by
  refine ⟨first.1, ?_⟩
  intro run holds n hp
  obtain ⟨m, hm, hq⟩ := first.2 run holds n hp
  obtain ⟨k, hk, hr⟩ := second.2 run holds m hq
  exact ⟨k, by omega, hr⟩

theorem leadsTo_of_imp {σ α : Type} {init : σ} {step : σ → α → σ} {assumed : (Nat → α) → Prop}
    {p q : σ → Prop} (possible : ∃ run, assumed run) (implies : ∀ s, p s → q s) :
    leadsTo init step assumed p q :=
  ⟨possible, fun _ _ n hp => ⟨n, Nat.le_refl n, implies _ hp⟩⟩

theorem leadsTo_or {σ α : Type} {init : σ} {step : σ → α → σ} {assumed : (Nat → α) → Prop}
    {p₁ p₂ q : σ → Prop} (first : leadsTo init step assumed p₁ q)
    (second : leadsTo init step assumed p₂ q) :
    leadsTo init step assumed (fun s => p₁ s ∨ p₂ s) q :=
  ⟨first.1, fun run holds n hp => hp.elim (first.2 run holds n) (second.2 run holds n)⟩

theorem eventually_of_leadsTo {σ α : Type} {init : σ} {step : σ → α → σ}
    {assumed : (Nat → α) → Prop} {p q : σ → Prop} (starts : p init)
    (leads : leadsTo init step assumed p q) : eventually init step assumed q := by
  refine ⟨leads.1, ?_⟩
  intro run holds
  obtain ⟨m, _, hq⟩ := leads.2 run holds 0 starts
  exact ⟨m, hq⟩

end Temporal
