import Axiom.Basic


@[main]
private lemma main
  [AddGroup α]
  [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {x y : α}
-- given
  (h : -x ≥ -y) :
-- imply
  x ≤ y := by
-- proof
  exact le_of_neg_le_neg h


-- created on 2025-03-20
