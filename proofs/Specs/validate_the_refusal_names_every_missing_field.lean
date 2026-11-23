import Mathlib

namespace Specs

theorem validate_the_refusal_names_every_missing_field.holds :
    validate_the_refusal_names_every_missing_field := by
  intro required present field
  simp [missing, List.mem_filter]

end Specs
