import Lemma.Basic


@[main]
private lemma main
  [Mul α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -(a * b) = -a * b := by
-- proof
  rw [neg_mul_eq_neg_mul]


-- created on 2024-07-01
