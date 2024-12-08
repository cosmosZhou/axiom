import Axiom.Algebra.Div_Neg.eq.NegDiv

namespace Algebra.NegDiv.eq

theorem Div_Neg
  [DivisionMonoid α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -(a / b) = a / -b := by
-- proof
  rw [Div_Neg.eq.NegDiv]


end Algebra.NegDiv.eq

-- created on 2024-07-01
