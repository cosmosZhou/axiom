import Axiom.Basic


@[main]
private lemma main
  [Lattice α]
  [AddGroup α]
  [AddLeftMono α]
  {x : α}
-- given
  (h : x < 0) :
-- imply
  |x| = -x := by
-- proof
  exact abs_of_neg h


-- created on 2025-03-20
