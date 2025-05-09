import sympy.sets.sets
import Axiom.Logic.All.of.All.All_Imp
import Axiom.Algebra.Root_Add_2.le.Sqrt.of.Ge_1
import Axiom.Algebra.LeSumS.of.All_Le
import Axiom.Algebra.Sum_Sqrt.le.SqrtMul_Sum.of.All_Ge_0.cauchy_schwarz
import Axiom.Algebra.Le.of.Le.Le
import Axiom.Algebra.EqMulS.of.Eq
import Axiom.Algebra.EqMulDiv.of.Ne_0
import Axiom.Algebra.Mul_Mul.comm
import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.Sum.ge.Zero.of.All_Ge_0
import Axiom.Algebra.GeDivS.of.Ge.Gt_0
import Axiom.Algebra.Gt_0.of.Ne_0
import Axiom.Algebra.EqDivMul.of.Ne_0
import Axiom.Algebra.EqSquareSqrt.of.Ge_0
import Axiom.Algebra.SqrtMulSquareS.eq.Mul.of.Ge_0.Ge_0
import Axiom.Algebra.Sqrt.ge.Zero
open Logic Algebra


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n ≠ 0)
  (h₁ : ∀ i ∈ range n, x i ≥ 1)
  (h₂ : (∑ i ∈ range n, x i) / n = x n) :
-- imply
  (∑ i ∈ range n, (x i) ^ (1 / (i + 2) : ℝ)) ≤ n * √(x n) := by
-- proof
  have : ∀ (t : ℝ) (i : ℕ), t ≥ 1 → (t ^ (1 / (i + 2) : ℝ) ≤ √t) := by 
    intro t i h
    apply Root_Add_2.le.Sqrt.of.Ge_1 h
  have := All.of.All.All_Imp.binary this h₁
  have h_Le := LeSumS.of.All_Le this
  have : ∀ t : ℝ, t ≥ 1 → t ≥ 0 := by 
    intro t h
    linarith
  have h_Ge_0 := All.of.All.All_Imp this h₁
  have := Sum_Sqrt.le.SqrtMul_Sum.of.All_Ge_0.cauchy_schwarz h_Ge_0
  simp only [Finset.card_range] at this
  have h_Le := Le.of.Le.Le h_Le this
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
