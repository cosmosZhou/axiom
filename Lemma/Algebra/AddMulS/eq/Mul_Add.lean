import Lemma.Basic


@[main]
private lemma main
  [Mul α] [Add α] [LeftDistribClass α]
  {x a b : α} :
-- imply
  x * a + x * b = x * (a + b) := by
-- proof
  rw [mul_add]


-- created on 2024-07-01
