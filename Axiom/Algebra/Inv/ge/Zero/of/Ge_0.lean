import Axiom.Algebra.GeInv_0.equ.Ge_0
open Algebra


@[main]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  {a : α}
-- given
  (h : a ≥ 0) :
-- imply
  a⁻¹ ≥ 0 :=
-- proof
  GeInv_0.equ.Ge_0.mpr h


-- created on 2025-01-14
