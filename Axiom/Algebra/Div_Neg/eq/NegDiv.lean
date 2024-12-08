import Axiom.Basic

namespace Algebra.Div_Neg.eq

theorem NegDiv
  [DivisionMonoid α] [HasDistribNeg α]
  {a b : α} :
-- imply
  a / -b = -(a / b) := by
-- proof
  rw [div_neg]


end Algebra.Div_Neg.eq

-- created on 2024-07-01
