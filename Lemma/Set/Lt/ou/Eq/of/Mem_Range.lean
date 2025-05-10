import sympy.sets.sets
import Lemma.Algebra.Lt.ou.Eq.of.Le
import Lemma.Algebra.Le.of.Lt_Add_1
import Lemma.Set.Lt.of.Mem_Range
open Algebra Set


@[main]
private lemma main
  {n i : ℕ}
-- given
  (h : i ∈ Finset.range (n + 1)) :
-- imply
  i < n ∨ i = n := by
-- proof
  apply Lt.ou.Eq.of.Le
  apply Le.of.Lt_Add_1
  apply Lt.of.Mem_Range h


-- created on 2025-04-26
