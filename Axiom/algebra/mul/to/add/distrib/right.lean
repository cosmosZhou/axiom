import Mathlib.Tactic

namespace algebra.mul.to.add.distrib

theorem right
  {R : Type*} [Mul R] [Add R] [RightDistribClass R]
  {x a b : R} :
-- imply
  (a + b) * x = a * x + b * x := by
-- proof
  rw [add_mul]
  -- ring



end algebra.mul.to.add.distrib
open algebra.mul.to.add.distrib
