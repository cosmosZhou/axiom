import Lemma.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  b ≠ a := by
-- proof
  exact h.symm


-- created on 2024-07-01
