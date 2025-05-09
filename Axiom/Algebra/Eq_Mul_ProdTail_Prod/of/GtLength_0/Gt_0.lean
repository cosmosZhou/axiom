import Axiom.Algebra.Ne.of.Gt
import Axiom.Algebra.Eq_Mul_ProdTail_Prod.of.NeLength_0.Ne_0
open Algebra


@[main]
private lemma main
  {shape : List ℕ}
-- given
  (h₀: shape.length > 0)
  (h₁: shape[0] > 0) :
-- imply
  shape.prod = shape[0] * shape.tail.prod := by
-- proof
  have h₀' := Ne.of.Gt h₀
  have h₁' := Ne.of.Gt h₁
  apply Eq_Mul_ProdTail_Prod.of.NeLength_0.Ne_0 h₀' h₁'


-- created on 2024-07-01
