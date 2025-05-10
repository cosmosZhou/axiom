import sympy.sets.sets
import Lemma.Algebra.GeSumS.of.All_Ge
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h : ∀ i ∈ range n, x i ≥ 0) :
-- imply
  ∑ i ∈ range n, (x i) ≥ 0 := by
-- proof
  have := GeSumS.of.All_Ge (n := n) (x := x) (y := fun _ => 0) h
  simp at this
  assumption


-- created on 2025-04-06
