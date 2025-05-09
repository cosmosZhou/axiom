import Axiom.Algebra.Ne.of.Gt
import Axiom.Algebra.Eq_DivProd_ProdTail.of.NeLength_0.Ne_0
open Algebra


@[main]
private lemma main
  {shape : List ℕ}
-- given
  (h₀: shape.length > 0)
  (h₁: shape[0] > 0) :
-- imply
  shape.tail.prod = shape.prod / shape[0] :=
-- proof
  Eq_DivProd_ProdTail.of.NeLength_0.Ne_0
    (Ne.of.Gt h₀)
    (Ne.of.Gt h₁)


-- created on 2024-07-01
