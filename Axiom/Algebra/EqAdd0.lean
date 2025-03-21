import Axiom.Basic


@[simp, main]
private lemma main
  [AddZeroClass M]
  {a : M} :
-- imply
  0 + a = a := by
-- proof
  rw [zero_add]


-- created on 2024-07-01
