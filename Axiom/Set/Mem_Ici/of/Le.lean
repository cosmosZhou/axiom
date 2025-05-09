import sympy.sets.sets
import Axiom.Set.Mem_Ici.of.Ge
open Set


@[main]
private lemma main
  [Preorder α]
  {x a : α}
-- given
  (h : a ≤ x) :
-- imply
  x ∈ Ici a :=
-- proof
  Mem_Ici.of.Ge h


-- created on 2025-04-27
