import Axiom.Basic

namespace Algebra.Gt_.Inv.Zero.equ

@[simp]
theorem Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {x : α} :
-- imply
  x⁻¹ > 0 ↔ x > 0:=
-- proof
  inv_pos


end Algebra.Gt_.Inv.Zero.equ

-- created on 2024-11-25
