import Axiom.Basic


@[main]
private lemma main
  [Semigroup α]
  {a b : α} :
-- imply
  a * b * c = a * (b * c) := by
-- proof
  rw [mul_assoc]


-- created on 2024-07-01
