import Axiom.Algebra.Sqrt.eq.Root_2
open Algebra


@[main]
private lemma main
  {x : ℝ} :
-- imply
  x ^ (1 / 2 : ℝ) = √x := by
-- proof
  -- Use the property of exponents to simplify the expression
  rw [Sqrt.eq.Root_2]


-- created on 2025-04-06
