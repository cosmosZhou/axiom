import sympy.core.power
import Lemma.Algebra.Square.ge.Zero
import Lemma.Algebra.EqSqrtSquare.of.Ge_0
open Algebra


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y ≥ 0) :
-- imply
  √(x² * y²) = x * y := by
-- proof
  have := Square.ge.Zero (a := x)
  have := Real.sqrt_mul this y²
  rw [EqSqrtSquare.of.Ge_0 h₀, EqSqrtSquare.of.Ge_0 h₁] at this
  assumption


-- created on 2025-04-06
