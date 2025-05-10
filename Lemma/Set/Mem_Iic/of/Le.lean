import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {x a : α}
-- given
  (h : x ≤ a) :
-- imply
  x ∈ Iic a :=
-- proof
  LowerSet.mem_Iic_iff.mpr h


-- created on 2025-04-27
