import Axiom.Basic


@[simp, main]
private lemma main
  [AddZeroClass α]
  {a : α} :
-- imply
  a + 0 = a := by
-- proof
  rw [add_zero]


-- created on 2024-07-01
