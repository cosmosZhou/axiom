import Axiom.Basic


@[main]
private lemma main
  [DivInvMonoid α]
  {a b c : α} :
-- imply
  a * b / c = a * (b / c) := by
-- proof
  rw [mul_div_assoc]


-- created on 2024-07-01
