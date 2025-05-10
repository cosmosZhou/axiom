import Lemma.Algebra.SquareSum_Mul.le.MulSumS_Square.cauchy_schwarz
import Lemma.Algebra.Mul.comm
open Algebra


@[main]
private lemma main
  [DecidableEq ι]
  {x : ι → ℝ} :
-- imply
  (∑ i ∈ s, x i)² ≤ s.card * ∑ i ∈ s, (x i)² := by
-- proof
  have := SquareSum_Mul.le.MulSumS_Square.cauchy_schwarz (s := s) (a := x) (b := fun i => 1)
  norm_num at this
  rw [Mul.comm] at this
  assumption


-- created on 2025-04-06
