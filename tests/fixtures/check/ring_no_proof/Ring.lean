namespace Ring

/-- code: ring.py wrap -/
def wrap (input : Int × Int) : Int := input.1 % input.2

def wrap.inputs : List (Int × Int) :=
  [(7, 3), (-7, 3), (0, 3), (7, -3), (-7, -3)]

def in_range : Prop :=
  ∀ index size : Int, 0 < size → 0 ≤ wrap (index, size) ∧ wrap (index, size) < size

end Ring
