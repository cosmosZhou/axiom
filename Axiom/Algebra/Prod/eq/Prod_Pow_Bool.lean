import Axiom.Logic.Bool.eq.Ite
import Axiom.Algebra.Pow_Ite.eq.Ite_PowS
open Logic Algebra


@[main]
private lemma main
  [Fintype ι]
  [CommMonoid α]
  [DecidableEq ι]
  {f : ι → α} :
-- imply
  ∏ i ∈ s, f i = ∏ i ∈ Set.univ, f i ^ Bool.toNat (i ∈ s) := by
-- proof
  simp only [Bool.eq.Ite]
  simp only [Pow_Ite.eq.Ite_PowS]
  simp [Finset.prod_ite]


-- created on 2025-04-29
-- updated on 2025-04-30
