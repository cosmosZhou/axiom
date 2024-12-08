import Axiom.Algebra.Gt.Gt_0.to.GtMulS
import Axiom.Algebra.Mul_Inv.eq.Div
import Axiom.Algebra.Gt_0.to.Inv.gt.Zero

namespace Algebra.Gt.Gt_0.to

theorem GtDivS
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
  (h1 : a > b)
  (h2 : x > 0) :
  a / x > b / x := by
  have h3 : x⁻¹ > 0 := Gt_0.to.Inv.gt.Zero h2
  have h4 := Gt.Gt_0.to.GtMulS h1 h3
  rw [
    Mul_Inv.eq.Div, Mul_Inv.eq.Div
  ] at h4
  exact h4


end Algebra.Gt.Gt_0.to

-- created on 2024-11-25
