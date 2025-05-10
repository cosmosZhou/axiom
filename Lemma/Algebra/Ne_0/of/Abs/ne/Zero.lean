import Lemma.Basic


@[main]
private lemma main
  [AddGroup α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
  {x : α}
-- given
  (h : |x| ≠ 0) :
-- imply
  x ≠ 0 := by
-- proof
  by_contra h
  have := abs_eq_zero.mpr h
  contradiction


-- created on 2025-04-18
