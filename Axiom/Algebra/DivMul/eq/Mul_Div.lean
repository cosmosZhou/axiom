import Axiom.Basic

namespace Algebra.DivMul.eq

theorem Mul_Div
  [DivInvMonoid α]
  {a b c : α} :
-- imply
  a * b / c = a * (b / c) := by
-- proof
  rw [mul_div_assoc]


end Algebra.DivMul.eq

-- created on 2024-07-01
