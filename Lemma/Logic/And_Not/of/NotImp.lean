import Lemma.Basic


@[main]
private lemma main
-- given
  (h : ¬(p → q)) :
-- imply
  p ∧ ¬q := by
-- proof
  simp at h
  exact h


-- created on 2024-07-01
