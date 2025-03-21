import Axiom.Algebra.Div_Neg.eq.NegDiv
open Algebra


@[main]
private lemma main
  [DivisionMonoid α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -(a / b) = a / -b := by
-- proof
  rw [Div_Neg.eq.NegDiv]


-- created on 2024-07-01
