import Axiom.Algebra.Square.eq.Mul
import Axiom.Algebra.Div_Mul.eq.DivDiv

namespace Algebra.Ne_0.to.Eq_.Div_Square


theorem Inv
  [Field α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a / a ^ 2 = a⁻¹ := by
-- proof
  rw [
    Square.eq.Mul,
    Div_Mul.eq.DivDiv
  ]
  simp [h]


end Algebra.Ne_0.to.Eq_.Div_Square

-- created on 2024-07-01
