import Lemma.Basic


/--
In a `DivInvMonoid`, division of `a` by `b` is defined as multiplication of `a` by the inverse of `b`.
This lemma confirms the equivalence `a / b = a * b⁻¹`, enabling the use of inverse properties in algebraic expressions involving division.
-/
@[main]
private lemma main
  [DivInvMonoid α]
  {a b : α} :
-- imply
  a / b = a * b⁻¹ := by
-- proof
  rw [div_eq_mul_inv]


-- created on 2024-07-01
-- updated on 2025-04-04
