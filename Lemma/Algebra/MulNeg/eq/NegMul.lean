import Lemma.Algebra.NegMul.eq.MulNeg
open Algebra


@[main]
private lemma main
  [Mul α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -a * b = -(a * b) := by
-- proof
  rw [NegMul.eq.MulNeg]


-- created on 2024-07-01
