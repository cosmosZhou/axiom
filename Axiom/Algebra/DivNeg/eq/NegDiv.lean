import Axiom.Basic

namespace Algebra.DivNeg.eq

theorem NegDiv
  [DivisionMonoid α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -a / b = -(a / b) := by
-- proof
  rw [neg_div]


end Algebra.DivNeg.eq

-- created on 2024-07-01
