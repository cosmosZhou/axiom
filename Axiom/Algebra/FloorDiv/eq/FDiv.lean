import Axiom.Algebra.FDiv.eq.FloorDiv
open Algebra


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  ⌊n / (d : ℚ)⌋ = n // d := by
-- proof
  rw [FDiv.eq.FloorDiv]


-- created on 2025-03-30
