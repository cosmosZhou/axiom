import Axiom.Algebra.Div.eq.Mul_Inv

namespace Algebra.Mul_Inv.eq

@[simp]
theorem Div
  [DivInvMonoid α]
  {a b : α} :
-- imply
  a * b⁻¹ = a / b := by
-- proof
  rw [Div.eq.Mul_Inv]


end Algebra.Mul_Inv.eq

-- created on 2024-07-01
