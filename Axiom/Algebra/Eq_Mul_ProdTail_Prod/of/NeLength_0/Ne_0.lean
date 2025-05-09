import Axiom.Algebra.Eq_Cons_Tail.of.Ne_0
import Axiom.Algebra.ProdCons.eq.Mul_Prod
open Algebra


@[main]
private lemma main
  {shape : List ℕ}
-- given
  (h₀: shape.length ≠ 0)
  (h₁: shape[0] ≠ 0) :
-- imply
  shape.prod = shape[0] * shape.tail.prod := by
-- proof
  -- Use the product property
  have h_prod : (shape[0]::shape.tail).prod = shape[0] * shape.tail.prod := by
    simp [ProdCons.eq.Mul_Prod]
  have h_cons := Eq_Cons_Tail.of.Ne_0 h₀
  rw [h_cons.symm] at h_prod
  exact h_prod


-- created on 2024-07-01
