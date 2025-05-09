import sympy.core.power
import Axiom.Algebra.EqSquareSqrt.of.Ge_0
import Axiom.Algebra.Ge.of.Gt
open Algebra


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  (√x)² = x := by
-- proof
  have := Ge.of.Gt h
  apply EqSquareSqrt.of.Ge_0 this


-- created on 2025-04-06
