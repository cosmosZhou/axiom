import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.EqSquareSqrt.of.Ge_0
import Lemma.Algebra.Sqrt.eq.Zero.of.Lt_0
import Lemma.Algebra.Sqrt.gt.Zero.of.Gt_0
open Algebra


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x > y)
  (h₁ : x > 0) :
-- imply
  √x > √y := by
-- proof
  by_cases h : y < 0
  ·
    have := Sqrt.eq.Zero.of.Lt_0 h
    rw [this]
    apply Sqrt.gt.Zero.of.Gt_0 h₁
  ·
    have h := Ge.of.NotLt h
    -- Use the fact that the square root function is increasing on the positive real numbers.
    apply Real.lt_sqrt_of_sq_lt
    have := EqSquareSqrt.of.Ge_0 h
    rw [this]
    assumption


-- created on 2025-04-06
