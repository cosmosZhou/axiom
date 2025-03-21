import Axiom.Basic


@[main]
private lemma main
  [NonAssocSemiring α]
  {a : α} :
-- imply
  a + a = a * 2 := by
-- proof
  rw [mul_two]


-- created on 2024-11-28
