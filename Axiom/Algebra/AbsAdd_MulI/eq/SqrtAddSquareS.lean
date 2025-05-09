import sympy.core.numbers
import Axiom.Algebra.Mul.eq.Square
open Algebra


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  ‖x + I * y‖ = √(x² + y²) := by
-- proof
  dsimp [Norm.norm]
  simp [Complex.normSq]
  rw [Mul.eq.Square, Mul.eq.Square]

-- created on 2025-01-05
