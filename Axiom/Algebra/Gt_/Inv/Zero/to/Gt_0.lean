import Axiom.Algebra.Gt_.Inv.Zero.equ.Gt_0


namespace Algebra.Gt_.Inv.Zero.to

theorem Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α}
-- given
  (h : x⁻¹ > 0) :
-- imply
  x > 0 :=
-- proof
  Gt_.Inv.Zero.equ.Gt_0.mp h


end Algebra.Gt_.Inv.Zero.to

-- created on 2024-11-25
