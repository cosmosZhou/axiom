import Mathlib.Tactic

namespace algebra.mul_one

theorem simp
  {M : Type u} [MulOneClass M]
  {a : M}:
-- imply
  a * 1 = a := by
-- proof
  rw [mul_one]


end algebra.mul_one
open algebra.mul_one
