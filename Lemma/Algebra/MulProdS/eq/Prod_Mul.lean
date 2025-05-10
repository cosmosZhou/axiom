import Lemma.Algebra.Prod_Mul.eq.MulProdS
open Algebra


@[main]
private lemma main
  [DecidableEq ι]
  [CommMonoid α]
  {s : Finset ι}
  {a b : ι → α} :
-- imply
  (∏ i ∈ s, a i) * ∏ i ∈ s, b i = ∏ i ∈ s, a i * b i :=
-- proof
  Prod_Mul.eq.MulProdS.symm


-- created on 2025-04-28
