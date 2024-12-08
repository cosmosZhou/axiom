import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.Mul.comm

namespace Algebra.Div.eq

theorem MulInv
  [CommGroup α]
  {a b : α} :
-- imply
  a / b = b⁻¹ * a := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [Mul.comm]





end Algebra.Div.eq

-- created on 2024-11-29
