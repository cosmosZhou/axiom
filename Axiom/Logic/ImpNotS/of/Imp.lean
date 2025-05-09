import Axiom.Basic


@[main]
private lemma main
-- given
  (h : p → q) :
-- imply
  ¬q → ¬p := by
-- proof
  intro hq hp
  have := h hp
  contradiction


-- created on 2024-07-01
