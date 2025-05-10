import sympy.sets.sets
import Lemma.Set.Lt.ou.Eq.of.Mem_Range
import Lemma.Set.Mem_Range.of.Lt
open Set


@[main]
private lemma main
  {n i : ℕ}
-- given
  (h : i ∈ Finset.range (n + 1)) :
-- imply
  i ∈ Finset.range n ∨ i = n := by
-- proof
  have := Lt.ou.Eq.of.Mem_Range h
  cases' this with h_Lt h_Eq
  ·
    exact Or.inl (Mem_Range.of.Lt h_Lt)
  ·
    exact Or.inr h_Eq


-- created on 2025-04-26
