import Lemma.Basic


@[main]
private lemma main
  [AddGroup α]
  {a b : α}
-- given
  (h : a = b) :
-- imply
  a - b = 0 := by
-- proof
  apply sub_eq_zero.mpr h


-- created on 2025-03-20
