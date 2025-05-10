import sympy.sets.sets
import Lemma.Algebra.LeSumS.of.All_Le
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {x y : ℕ → ℝ}
-- given
  (h₀ : ∀ i ∈ range n, x i ≥ y i) :
-- imply
  ∑ i ∈ range n, x i ≥ ∑ i ∈ range n, y i := by
-- proof
  exact LeSumS.of.All_Le (n := n) (x := y) (y := x) h₀


-- created on 2025-04-06
