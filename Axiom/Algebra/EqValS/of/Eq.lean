import Axiom.Basic


@[main]
private lemma main
  {a b : List.Vector α n}
-- given
  (h : a = b) :
-- imply
  a.val = b.val := by
-- proof
  rw [h]


-- created on 2025-05-08
