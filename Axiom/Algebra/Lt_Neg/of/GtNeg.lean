import Axiom.Algebra.EqNegNeg
import Axiom.Algebra.Lt.of.GtNegS
open Algebra


@[main]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {x y : α}
-- given
  (h : -x > y) :
-- imply
  x < -y := by
-- proof
  apply Lt.of.GtNegS
  rw [EqNegNeg]
  assumption


-- created on 2025-03-20
