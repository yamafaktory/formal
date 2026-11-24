import Formal.Temporal

namespace Live

inductive Action where
  | inc
  | reset

structure State where
  count : Nat

def init : State := ⟨0⟩

def step (s : State) : Action → State
  | .inc => ⟨min (s.count + 1) 2⟩
  | .reset => ⟨0⟩

def positive : State → Prop := fun s => 0 < s.count

def a_fair_reset_empties_it : Prop :=
  Temporal.leadsTo init step (Temporal.fair Action.reset) positive (fun s => s.count = 0)

def two_comes : Prop :=
  Temporal.eventually init step (fun run => Temporal.fair Action.inc run ∧ Temporal.fair Action.reset run)
    (fun s => s.count = 2)

def unfair : Prop := Temporal.leadsTo Live.init Live.step (fun _ => True) (fun s => 0 < s.count) (fun s => s.count = 0)

def other_machine : Prop := Temporal.eventually (0 : Nat) (fun n (_ : Action) => n) (fun _ => True) (fun n => n = 1)

def any_assumption : Prop :=
  Temporal.leadsTo init step (fun run => run 0 = Action.inc) positive (fun s => s.count = 0)

end Live
