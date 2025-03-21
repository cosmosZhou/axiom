import Axiom.Basic


@[main]
private lemma main
  [DivisionCommMonoid α]
  {a b c : α} :
-- imply
  a / (b * c) = a / b / c := by
-- proof
  rw [div_mul_eq_div_div]


-- created on 2024-07-01
