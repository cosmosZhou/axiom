import Axiom.Algebra.SquareSum_Sqrt.le.Mul_Sum.of.All_Ge_0.cauchy_schwarz
import Axiom.Algebra.Le_Sqrt.of.LeSquare
open Algebra


@[main]
private lemma main
  {s : Finset ℕ}
  {x : ℕ → ℝ}
-- given
  (h : ∀ i ∈ s, x i ≥ 0) :
-- imply
  ∑ i ∈ s, √(x i) ≤ √(s.card * ∑ i ∈ s, x i) := by
-- proof
  have := SquareSum_Sqrt.le.Mul_Sum.of.All_Ge_0.cauchy_schwarz (s := s) (x := x) h
  have := Le_Sqrt.of.LeSquare this
  assumption


-- created on 2025-04-06
-- updated on 2025-04-28
