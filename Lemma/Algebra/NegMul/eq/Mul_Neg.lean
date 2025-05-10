import Lemma.Algebra.Mul_Neg.eq.NegMul
open Algebra


@[main]
private lemma main
  [Mul α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -(a * b) = a * -b := by
-- proof
  rw [Mul_Neg.eq.NegMul]


-- created on 2024-07-01
