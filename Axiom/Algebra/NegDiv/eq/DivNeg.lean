import Axiom.Algebra.DivNeg.eq.NegDiv

namespace Algebra.NegDiv.eq

theorem DivNeg
  [DivisionMonoid α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -(a / b) = -a / b := by
-- proof
  rw [DivNeg.eq.NegDiv]


end Algebra.NegDiv.eq

-- created on 2024-07-01
