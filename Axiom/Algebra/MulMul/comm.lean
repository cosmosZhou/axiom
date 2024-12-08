import Axiom.Algebra.Mul.comm
import Axiom.Algebra.Mul_Mul.eq.MulMul

namespace Algebra.MulMul

theorem comm
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = a * c * b := by
-- proof
  rw [Mul.comm (b := c)]
  rw [Mul.comm (b := c)]
  rw [Mul_Mul.eq.MulMul]


end Algebra.MulMul

-- created on 2024-11-29
