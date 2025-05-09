import Axiom.Basic


@[main]
private lemma main
-- given
  (h : p ↔ q) :
-- imply
  ¬p ↔ ¬q := by
-- proof
  rw [h]


-- created on 2024-07-01
