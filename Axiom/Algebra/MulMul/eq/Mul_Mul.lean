import Axiom.Basic

namespace Algebra.MulMul.eq

theorem Mul_Mul
  [Semigroup α]
  {a b : α} :
-- imply
  a * b * c = a * (b * c) := by
-- proof
  rw [mul_assoc]


end Algebra.MulMul.eq

-- created on 2024-07-01
