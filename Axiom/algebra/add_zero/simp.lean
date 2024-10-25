import Mathlib.Tactic

namespace algebra.add_zero

theorem simp
  {M : Type u} [AddZeroClass M]
  {a : M}:
-- imply
  a + 0 = a := by
-- proof
  rw [add_zero]


end algebra.add_zero
open algebra.add_zero
