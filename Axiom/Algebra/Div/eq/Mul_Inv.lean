import Axiom.Basic


@[main]
private lemma main
  [DivInvMonoid α]
  {a b : α} :
-- imply
  a / b = a * b⁻¹ := by
-- proof
  rw [div_eq_mul_inv]


-- created on 2024-07-01
