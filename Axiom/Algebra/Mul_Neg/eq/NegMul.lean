import Axiom.Basic

namespace Algebra.Mul_Neg.eq

theorem NegMul
  [Mul α] [HasDistribNeg α]
  {a b : α} :
-- imply
  a * -b = -(a * b) := by
-- proof
  rw [mul_neg]


end Algebra.Mul_Neg.eq

-- created on 2024-07-01
