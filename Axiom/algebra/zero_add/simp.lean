import Mathlib.Tactic

namespace algebra.zero_add

theorem simp
  {M : Type u} [AddZeroClass M]
  {a : M}:
-- imply
  0 + a = a := by
-- proof
  rw [zero_add]


end algebra.zero_add
open algebra.zero_add
