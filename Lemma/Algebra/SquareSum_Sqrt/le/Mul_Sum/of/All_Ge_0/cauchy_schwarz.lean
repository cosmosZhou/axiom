import Lemma.Algebra.SquareSum.le.Mul_Sum_Square.cauchy_schwarz
import Lemma.Algebra.EqSquareSqrt.of.Ge_0
import Lemma.Logic.All.of.All.All_Imp
import Lemma.Algebra.EqSumS.of.All_Eq
open Algebra Logic


@[main]
private lemma main
  {s : Finset ℕ}
  {x : ℕ → ℝ}
-- given
  (h : ∀ i ∈ s, x i ≥ 0) :
-- imply
  (∑ i ∈ s, √(x i))² ≤ s.card * ∑ i ∈ s, x i := by
-- proof
  have h_Le := SquareSum.le.Mul_Sum_Square.cauchy_schwarz (s := s) (x := fun i => √(x i))
  have : ∀ t : ℝ, t ≥ 0 → (√t)² = t := by
    intro t h
    apply EqSquareSqrt.of.Ge_0 h
  have := All.of.All.All_Imp.finset this h
  have := EqSumS.of.All_Eq this
  rw [this] at h_Le
  assumption


-- created on 2025-04-06
-- updated on 2025-04-28
