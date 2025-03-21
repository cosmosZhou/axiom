import Axiom.Algebra.GtInv_0.equ.Gt_0
open Algebra


@[main]
private lemma main
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
  GtInv_0.equ.Gt_0.mpr h


-- created on 2024-11-25
