import Axiom.Algebra.NegMul.eq.MulNeg

namespace Algebra.MulNeg.eq

theorem NegMul
  [Mul α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -a * b = -(a * b) := by
-- proof
  rw [NegMul.eq.MulNeg]


end Algebra.MulNeg.eq

-- created on 2024-07-01
