import sympy.sets.sets
import Axiom.Set.Mem_Iio.of.Lt
open Set


@[main]
private lemma main
  [Preorder α]
  {x a : α}
-- given
  (h : a > x) :
-- imply
  x ∈ Iio a :=
-- proof
  Mem_Iio.of.Lt h


-- created on 2025-04-27
