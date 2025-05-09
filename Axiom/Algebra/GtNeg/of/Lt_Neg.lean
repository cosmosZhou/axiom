import Axiom.Algebra.EqNegNeg
import Axiom.Algebra.Gt.of.LtNegS
open Algebra


@[main]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {a : α}
-- given
  (h : a < -b) :
-- imply
  -a > b := by
-- proof
  apply Gt.of.LtNegS
  rw [EqNegNeg]
  assumption


-- created on 2025-03-29
