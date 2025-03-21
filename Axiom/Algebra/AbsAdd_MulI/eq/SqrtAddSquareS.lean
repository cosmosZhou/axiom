import Axiom.Algebra.Mul.eq.Square
open Algebra


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  abs (x + I * y) = √(x² + y²) := by
-- proof
  simp [Root.sqrt]
  rw [Complex.abs_def]
  simp [normSq]
  rw [Mul.eq.Square, Mul.eq.Square]


-- created on 2025-01-05
