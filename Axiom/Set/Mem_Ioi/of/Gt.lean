import sympy.sets.sets
import Axiom.Basic


@[main]
private lemma main
  [Preorder α]
  {x a : α}
-- given
  (h : x > a) :
-- imply
  x ∈ Ioi a :=
-- proof
  UpperSet.mem_Ioi_iff.mpr h


-- created on 2025-04-27
