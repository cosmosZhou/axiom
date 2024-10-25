import Mathlib.Tactic

namespace algebra.one_mul

theorem simp
  {M : Type u} [MulOneClass M]
  {a : M}:
-- imply
  1 * a = a := by
-- proof
  rw [one_mul]


end algebra.one_mul
open algebra.one_mul
