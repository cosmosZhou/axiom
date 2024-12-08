import Axiom.Basic

namespace Algebra.NegMul.eq

theorem MulNeg
  [Mul α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -(a * b) = -a * b := by
-- proof
  rw [neg_mul_eq_neg_mul]


end Algebra.NegMul.eq

-- created on 2024-07-01
