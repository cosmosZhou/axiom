import Axiom.Basic

namespace Algebra.Div_Mul.eq

theorem DivDiv
  [DivisionCommMonoid α]
  {a b c : α} :
-- imply
  a / (b * c) = a / b / c := by
-- proof
  rw [div_mul_eq_div_div]


end Algebra.Div_Mul.eq

-- created on 2024-07-01
