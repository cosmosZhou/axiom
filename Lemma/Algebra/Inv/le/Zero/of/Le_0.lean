import Lemma.Algebra.Inv.le.Zero.is.Le_0
open Algebra


@[main]
private lemma main
  [GroupWithZero α]
  [LinearOrder α]
  [ZeroLEOneClass α]
  [PosMulMono α]
  {a : α}
-- given
  (h : a ≤ 0) :
-- imply
  a⁻¹ ≤ 0 :=
-- proof
  Inv.le.Zero.is.Le_0.mpr h


-- created on 2025-03-30
