import Axiom.Algebra.Ne.of.Gt
import Axiom.Algebra.Eq_Mul_ProdTail_Prod.of.NeLength_0.Ne_0
open Algebra


@[main]
private lemma main
  {shape : List ℕ}
-- given
  (h1: shape.length > 0)
  (h2: shape[0] > 0) :
-- imply
  shape.prod = shape[0] * shape.tail.prod := by
-- proof
  have h1' := Ne.of.Gt h1
  have h2' := Ne.of.Gt h2
  apply Eq_Mul_ProdTail_Prod.of.NeLength_0.Ne_0 h1' h2'


-- created on 2024-07-01
