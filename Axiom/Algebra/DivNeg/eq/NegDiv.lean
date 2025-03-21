import Axiom.Basic


@[main]
private lemma main
  [DivisionMonoid α] [HasDistribNeg α]
  {a b : α} :
-- imply
  -a / b = -(a / b) := by
-- proof
  rw [neg_div]


-- created on 2024-07-01
