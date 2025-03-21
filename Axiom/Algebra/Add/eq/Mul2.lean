import Axiom.Basic


@[simp, main]
private lemma main
  [NonAssocSemiring α]
  {a : α} :
-- imply
  a + a = 2 * a := by
-- proof
  rw [two_mul]


-- created on 2024-07-01
