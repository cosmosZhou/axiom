import Axiom.Basic


@[main]
private lemma main
  [AddGroup α]
  {a b : α}
-- given
  (h : a - b = 0) :
-- imply
  a = b := by
-- proof
  apply sub_eq_zero.mp h


-- created on 2025-03-30
