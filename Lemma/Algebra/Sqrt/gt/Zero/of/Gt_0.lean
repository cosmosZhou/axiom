import Lemma.Algebra.Sqrt.ge.Zero
import Lemma.Algebra.Sqrt.ne.Zero.of.Gt_0
import Lemma.Algebra.Gt.of.Ge.Ne
open Algebra


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  √x > 0 := by
-- proof
  have := Sqrt.ge.Zero (x := x)
  have h_Ne := Sqrt.ne.Zero.of.Gt_0 h
  exact Gt.of.Ge.Ne this h_Ne


-- created on 2025-04-06
