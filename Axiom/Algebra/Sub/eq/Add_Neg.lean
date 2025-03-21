import Axiom.Basic


@[main]
private lemma main
  [SubNegMonoid α]
  {a b : α} :
-- imply
  a - b = a + -b := by
-- proof
  rw [sub_eq_add_neg]


-- created on 2024-07-01
