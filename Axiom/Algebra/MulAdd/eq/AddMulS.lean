import Axiom.Basic


@[main]
private lemma main
  [Mul α] [Add α] [RightDistribClass α]
  {a b c : α} :
-- imply
  (a + b) * c = a * c + b * c := by
-- proof
  rw [right_distrib]


-- created on 2024-07-01
