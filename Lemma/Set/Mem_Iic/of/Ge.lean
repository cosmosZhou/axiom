import sympy.sets.sets
import Lemma.Set.Mem_Iic.of.Le
open Set


@[main]
private lemma main
  [Preorder α]
  {x a : α}
-- given
  (h : a ≥ x) :
-- imply
  x ∈ Iic a :=
-- proof
  Mem_Iic.of.Le h


-- created on 2025-04-27
