import sympy.sets.sets
import Axiom.Set.Mem_Ioi.of.Gt
open Set


@[main]
private lemma main
  [Preorder α]
  {x a : α}
-- given
  (h : a < x) :
-- imply
  x ∈ Ioi a :=
-- proof
  Mem_Ioi.of.Gt h


-- created on 2025-04-27
