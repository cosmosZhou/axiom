import Axiom.Algebra.Lt.of.GtNegS
import Axiom.Algebra.EqNegNeg
open Algebra


@[main]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {a : α}
-- given
  (h : a > -b) :
-- imply
  -a < b := by
-- proof
  apply Lt.of.GtNegS
  rw [EqNegNeg]
  assumption


-- created on 2025-03-29
