import sympy.sets.sets
import Lemma.Algebra.EqCeil.of.Lt.et.Le
import Lemma.Set.Lt.of.Mem_Ioc
import Lemma.Set.Le.of.Mem_Ioc
open Algebra Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {x : α}
-- given
  (h : x ∈ Ioc (z - 1 : α) z) :
-- imply
  ⌈x⌉ = z := by
-- proof

  apply EqCeil.of.Lt.et.Le
  ·
    exact Lt.of.Mem_Ioc h
  ·
    exact Le.of.Mem_Ioc h


-- created on 2025-05-04
