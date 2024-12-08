import Axiom.Algebra.Div_Mul.eq.DivDiv

namespace Algebra.DivDiv.eq

theorem Div_Mul
  [DivisionCommMonoid α]
  {a b c : α} :
-- imply
  a / b / c = a / (b * c)  := by
-- proof
  rw [Div_Mul.eq.DivDiv]


end Algebra.DivDiv.eq

-- created on 2024-07-01
