import Axiom.Algebra.Prod.eq.Prod_Pow_Bool
import Axiom.Algebra.MulProdS.eq.Prod_Mul
import Axiom.Algebra.MulPowS.eq.Pow_Add
import Axiom.Set.BoolMem.eq.AddBoolSMem
open Algebra Set


@[main]
private lemma main
  [Fintype ι]
  [DecidableEq ι]
  [CommMonoid α]
  {A B : Finset ι}
  {f : ι → α} :
-- imply
  ∏ x ∈ A, f x = (∏ x ∈ A ∩ B, f x) * ∏ x ∈ A \ B, f x := by
-- proof
  rw [Prod.eq.Prod_Pow_Bool]
  rw [Prod.eq.Prod_Pow_Bool (s := A ∩ B)]
  rw [Prod.eq.Prod_Pow_Bool (s := A \ B)]
  rw [MulProdS.eq.Prod_Mul]
  simp only [MulPowS.eq.Pow_Add]
  simp only [← BoolMem.eq.AddBoolSMem.finset]


-- created on 2025-04-30
-- updated on 2025-05-01
