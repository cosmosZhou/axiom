import Axiom.Basic


@[main]
private lemma main
  [Mul α] [HasDistribNeg α]
  {a b : α} :
-- imply
  a * -b = -(a * b) := by
-- proof
  rw [mul_neg]


-- created on 2024-07-01
