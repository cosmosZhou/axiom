import Axiom.Algebra.Gt_.Inv.Zero.equ.Gt_0

namespace Algebra.Gt_0.to.Inv.gt

theorem Zero
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  x⁻¹ > 0 :=
-- proof
  Gt_.Inv.Zero.equ.Gt_0.mpr h


end Algebra.Gt_0.to.Inv.gt

-- created on 2024-11-25
