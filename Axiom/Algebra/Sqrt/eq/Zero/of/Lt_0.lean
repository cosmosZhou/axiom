import Axiom.Algebra.Le.of.Lt
import Axiom.Algebra.Sqrt.eq.Zero.of.Le_0
open Algebra


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  √x = 0 := by
-- proof
  have := Le.of.Lt h
  apply Sqrt.eq.Zero.of.Le_0 this


-- created on 2025-04-06
