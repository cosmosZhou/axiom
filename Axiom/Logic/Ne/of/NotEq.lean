import Axiom.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : ¬a = b) :
-- imply
  a ≠ b := by
-- proof
  exact h


-- created on 2025-03-15
