import Lemma.Algebra.Inv.ge.Zero.is.Ge_0
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
  Inv.ge.Zero.is.Ge_0.mpr h


-- created on 2025-01-14
