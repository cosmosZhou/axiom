import sympy.sets.sets
import Axiom.Set.EqCeil.of.Mem_Ioc
open Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : x ∈ Ioc 0 1) :
-- imply
  ⌈x⌉ = 1 := by
-- proof
  apply EqCeil.of.Mem_Ioc
  simp
  assumption


-- created on 2025-05-04
