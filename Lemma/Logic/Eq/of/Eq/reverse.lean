import Lemma.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : a = b) :
-- imply
  b = a := by
-- proof
  apply Eq.symm h


-- created on 2024-07-01
