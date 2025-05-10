import Lemma.Algebra.Abs.ne.Zero.of.Ne_0
import Lemma.Algebra.Abs.ge.Zero
import Lemma.Algebra.Gt.of.Ge.Ne
open Algebra


@[main]
private lemma main
  [AddGroup α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  |a| > 0 := by
-- proof
  have h_Ne := Abs.ne.Zero.of.Ne_0 h
  have h_Ge := Abs.ge.Zero (a := a)
  apply Gt.of.Ge.Ne h_Ge h_Ne


-- created on 2025-04-20
