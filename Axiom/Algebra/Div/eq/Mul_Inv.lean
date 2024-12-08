import Axiom.Basic

namespace Algebra.Div.eq

theorem Mul_Inv
  [DivInvMonoid α]
  {a b : α} :
-- imply
  a / b = a * b⁻¹ := by
-- proof
  rw [div_eq_mul_inv]



end Algebra.Div.eq

-- created on 2024-07-01
