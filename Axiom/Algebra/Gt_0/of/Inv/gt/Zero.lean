import Axiom.Algebra.Inv.gt.Zero.is.Gt_0
open Algebra


@[main]
private lemma main
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
  Inv.gt.Zero.is.Gt_0.mp h


-- created on 2024-11-25
