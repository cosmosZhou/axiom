import Axiom.Basic


@[main]
private lemma main
  [DivisionCommMonoid α]
  {a b c : α} :
-- imply
  a * b / c = a / c * b := by
-- proof
  rw [mul_div_right_comm]


-- created on 2024-07-01
