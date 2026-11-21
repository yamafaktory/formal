import Mathlib

namespace Pystr

theorem is_space_the_separator_control_range_is_space.holds :
    is_space_the_separator_control_range_is_space := by
  intro c lo hi
  simp only [isSpace]
  have : c.toNat = 0x1c ∨ c.toNat = 0x1d ∨ c.toNat = 0x1e ∨ c.toNat = 0x1f := by omega
  rcases this with h | h | h | h <;> simp [h]

end Pystr
