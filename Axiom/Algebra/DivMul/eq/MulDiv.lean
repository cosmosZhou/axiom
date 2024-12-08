import Axiom.Basic

namespace Algebra.DivMul.eq

theorem MulDiv
  [DivisionCommMonoid α]
  {a b c : α} :
-- imply
  a * b / c = a / c * b := by
-- proof
  rw [mul_div_right_comm]


end Algebra.DivMul.eq

-- created on 2024-07-01
