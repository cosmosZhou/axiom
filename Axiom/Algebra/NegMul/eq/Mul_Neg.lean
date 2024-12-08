import Axiom.Algebra.Mul_Neg.eq.NegMul

namespace Algebra.NegMul.eq

theorem Mul_Neg
  [Mul α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -(a * b) = a * -b := by
-- proof
  rw [Mul_Neg.eq.NegMul]


end Algebra.NegMul.eq

-- created on 2024-07-01
