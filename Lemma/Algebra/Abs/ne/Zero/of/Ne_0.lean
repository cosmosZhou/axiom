import Lemma.Basic


@[main]
private lemma main
  [AddGroup α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  |a| ≠ 0 := by
-- proof
  by_contra h
  have := abs_eq_zero.mp h
  contradiction


-- created on 2025-01-14
