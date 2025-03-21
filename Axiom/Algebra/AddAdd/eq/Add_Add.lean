import Axiom.Basic


@[main]
private lemma main
  [AddSemigroup α]
  {a b : α} :
-- imply
  a + b + c = a + (b + c) := by
-- proof
  rw [add_assoc]


-- created on 2024-07-01
