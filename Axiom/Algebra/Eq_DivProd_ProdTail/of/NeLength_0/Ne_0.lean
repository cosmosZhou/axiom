import Axiom.Algebra.Eq_Mul_ProdTail_Prod.of.NeLength_0.Ne_0
import Axiom.Algebra.EqDivS.of.Eq
open Algebra


@[main]
private lemma main
  {shape : List ℕ}
-- given
  (h1: shape.length ≠ 0)
  (h2: shape[0] ≠ 0) :
-- imply
  shape.tail.prod = shape.prod / shape[0] := by
-- proof
  -- Use the product property
  have h_prod := Eq_Mul_ProdTail_Prod.of.NeLength_0.Ne_0 h1 h2
  -- divide both sides by shape[0]
  have h_div := EqDivS.of.Eq h_prod shape[0]
  simp [h2] at h_div
  -- h_div : shape.prod / shape[0] = shape.tail.prod
  exact h_div.symm


-- created on 2024-07-01
