import Axiom.Algebra.DivMul.eq.Mul_Div

namespace Algebra.Mul_Div.eq

theorem DivMul
  [DivInvMonoid α]
  {a b c : α} :
-- imply
  a * (b / c) = a * b / c := by
-- proof
  rw [DivMul.eq.Mul_Div]


end Algebra.Mul_Div.eq

-- created on 2024-07-01
