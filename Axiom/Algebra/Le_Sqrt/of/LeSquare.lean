import sympy.core.power
import Axiom.Algebra.Sqrt.ge.Zero
import Axiom.Algebra.Square.ge.Zero
import Axiom.Algebra.Ge.of.Ge.Ge
import Axiom.Algebra.Eq.of.Le.Ge
import Axiom.Algebra.Eq_0.of.Square.le.Zero
open Algebra


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x² ≤ y) :
-- imply
  x ≤ √y := by
-- proof
  -- We need to show that x ≤ √y given x² ≤ y. We consider two cases: x ≥ 0 and x < 0.
  cases' le_total 0 x with hx hx
  ·
    -- For each case, we use the fact that the square root of a non-negative number is non-negative.
    cases' le_total 0 y with hy hy
    ·
      -- Case 1: x ≥ 0 and y ≥ 0
      -- Since x ≥ 0 and y ≥ 0, we can take the square root of both sides of x² ≤ y.
      apply (Real.le_sqrt hx hy).mpr h
    ·
      -- Case 2: x ≥ 0 and y < 0
      -- This case is impossible because y < 0 contradicts x² ≤ y (since x² is always non-negative).
      have := Square.ge.Zero (a := x)
      have := Ge.of.Ge.Ge h this
      have := Eq.of.Le.Ge hy this
      rw [this]
      rw [this] at h
      norm_num
      have := Eq_0.of.Square.le.Zero h 
      linarith
  ·
    have := Sqrt.ge.Zero (x := y)
    linarith


-- created on 2025-04-06
