import sympy.core.relational
import sympy.core.power
import Axiom.Algebra.EqDivS.of.Eq
import Axiom.Algebra.SquareDiv.eq.DivSquareS
import Axiom.Algebra.Le.of.Gt_0.LeMulS
import Axiom.Algebra.Mul_Mul.eq.MulMul
import Axiom.Algebra.EqMul_Div.of.Ne_0
import Axiom.Algebra.Square.le.MulMul4.of.Ge_0.AddAddMul_Square.ge.Zero
import Axiom.Algebra.Sum_Square.ge.Zero
import Axiom.Algebra.AddAddMulSquare_Sum.ge.Zero
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.MulMul.eq.Mul_Mul
open Algebra


@[main]
private lemma main
  [DecidableEq ι]
  {a b : ι → ℝ} :
-- imply
  (∑ i ∈ s, a i * b i)² ≤ (∑ i ∈ s, (a i)²) * ∑ i ∈ s, (b i)² := by
-- proof
  denote hA : A = ∑ i ∈ s, (a i)²
  denote hB : B = 2 * ∑ i ∈ s, a i * b i
  have hB := EqDivS.of.Eq hB 2
  norm_num at hB
  denote hC : C = ∑ i ∈ s, (b i)²
  rw [← hA, ← hC, ← hB]
  rw [SquareDiv.eq.DivSquareS]
  norm_num
  apply Le.of.Gt_0.LeMulS (by norm_num : (4 : ℝ) > 0)
  rw [Mul_Mul.eq.MulMul]
  rw [EqMul_Div.of.Ne_0 (by norm_num : (4 : ℝ) ≠ 0)]
  apply Square.le.MulMul4.of.Ge_0.AddAddMul_Square.ge.Zero
  ·
    intro x
    have := AddAddMulSquare_Sum.ge.Zero (s := s) (x := x) (a := a) (b := b)
    rw [← hA, ← hC, ← hB] at this
    rw [Mul.comm (a := 2)] at this
    rw [MulMul.eq.Mul_Mul] at this
    rw [EqMul_Div.of.Ne_0 (by norm_num : (2 : ℝ) ≠ 0)] at this
    rw [Mul.comm] at this
    rw [Mul.comm (a := x)] at this
    assumption
  ·
    apply Sum_Square.ge.Zero


-- created on 2025-04-06
