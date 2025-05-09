import sympy.sets.sets
import Axiom.Logic.All.of.All.All_Imp
import Axiom.Algebra.Sum_Sqrt.le.SqrtMul_Sum.of.All_Ge_0.cauchy_schwarz
import Axiom.Algebra.EqMulS.of.Eq
import Axiom.Algebra.EqMulDiv.of.Ne_0
import Axiom.Algebra.Mul_Mul.comm
import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.Sum.ge.Zero.of.All_Ge_0
import Axiom.Algebra.Gt_0.of.Ne_0
import Axiom.Algebra.GeDivS.of.Ge.Gt_0
import Axiom.Algebra.EqDivMul.of.Ne_0
import Axiom.Algebra.EqSquareSqrt.of.Ge_0
import Axiom.Algebra.SqrtMulSquareS.eq.Mul.of.Ge_0.Ge_0
import Axiom.Algebra.Sqrt.ge.Zero
open Logic Algebra


/--
Given a non-zero natural number `n` and a sequence `x` of real numbers where each element is at least 1, if the average of the first `n` elements equals the `n`-th element, then the sum of the square roots of the first `n` elements is bounded above by `n` times the square root of the `n`-th element. 
This result leverages the Cauchy-Schwarz inequality and algebraic manipulations under the specified conditions.
-/
@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n ≠ 0)
  (h₁ : ∀ i ∈ range n, x i ≥ 1)
  (h₂ : (∑ i ∈ range n, x i) / n = x n) :
-- imply
  (∑ i ∈ range n, √(x i)) ≤ n * √(x n) := by
-- proof
  have : ∀ t : ℝ, t ≥ 1 → t ≥ 0 := by 
    intro t h
    linarith
  have h_Ge_0 := All.of.All.All_Imp this h₁
  have h_Le := Sum_Sqrt.le.SqrtMul_Sum.of.All_Ge_0.cauchy_schwarz h_Ge_0
  simp only [Finset.card_range] at h_Le
  have h_Eq := EqMulS.of.Eq h₂ n
  rw [EqMulDiv.of.Ne_0 (by simp [h₀] : (n : ℝ) ≠ 0)] at h_Eq
  rw [h_Eq] at h_Le
  rw [Mul_Mul.comm] at h_Le
  rw [Mul.eq.Square] at h_Le
  rw [Mul.comm] at h_Le
  have := Sum.ge.Zero.of.All_Ge_0 h_Ge_0
  have h_n : (n : ℝ) > 0 := by 
    simp
    apply Gt_0.of.Ne_0 h₀
  have := GeDivS.of.Ge.Gt_0 this h_n
  norm_num at this
  rw [h_Eq] at this
  rw [EqDivMul.of.Ne_0 (by simp [h₀] : (n : ℝ) ≠ 0)] at this
  have := EqSquareSqrt.of.Ge_0 this
  rw [← this] at h_Le
  rw [SqrtMulSquareS.eq.Mul.of.Ge_0.Ge_0 (by norm_num) (by apply Sqrt.ge.Zero)] at h_Le
  assumption


-- created on 2025-04-06
-- updated on 2025-04-28
