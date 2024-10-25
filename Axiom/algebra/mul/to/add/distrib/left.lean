import Mathlib.Tactic

namespace algebra.mul.to.add.distrib

theorem left
  {x a b : ℝ} :
-- imply
  x * (a + b) = x * a + x * b := by
-- proof
  rw [mul_add]
  -- ring



end algebra.mul.to.add.distrib
open algebra.mul.to.add.distrib
