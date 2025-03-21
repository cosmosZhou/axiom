import Axiom.Algebra.DivNeg.eq.NegDiv
open Algebra


@[main]
private lemma main
  [DivisionMonoid α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -(a / b) = -a / b := by
-- proof
  rw [DivNeg.eq.NegDiv]


-- created on 2024-07-01
