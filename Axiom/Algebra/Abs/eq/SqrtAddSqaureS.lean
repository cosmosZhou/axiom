import Axiom.Algebra.Mul.eq.Square
open Algebra


@[main]
private lemma main
  {z : ℂ} :
-- imply
  abs z = √((re z)² + (im z)²) := by
-- proof
  simp [Complex.abs, normSq]
  rw [Mul.eq.Square, Mul.eq.Square]
  simp [Root.sqrt]


-- created on 2025-01-16
-- updated on 2025-01-17
