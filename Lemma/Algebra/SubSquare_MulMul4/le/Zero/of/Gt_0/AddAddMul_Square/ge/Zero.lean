import sympy.core.power
import Lemma.Algebra.DivNeg.eq.NegDiv
import Lemma.Algebra.SquareNeg.eq.Square
import Lemma.Algebra.SquareDiv.eq.DivSquareS
import Lemma.Algebra.SquareMul.eq.MulSquareS
import Lemma.Algebra.Square.eq.Mul
import Lemma.Algebra.Mul_Mul.eq.MulMul
import Lemma.Algebra.Mul_Div.eq.DivMul
import Lemma.Algebra.Mul.comm
import Lemma.Algebra.Add_Neg.eq.Sub
import Lemma.Algebra.Mul.eq.Square
import Lemma.Algebra.SubDivS.eq.DivMul_Sub.of.Ne_0.Ne_0
import Lemma.Algebra.Ne.of.Gt
import Lemma.Algebra.SubMulS.eq.MulSub
import Lemma.Algebra.NegMul.eq.MulNeg
import Lemma.Algebra.DivMulS.eq.Div.of.Ne_0
import Lemma.Algebra.AddNeg.eq.Sub
import Lemma.Algebra.LeMulS.of.Gt_0.Le
import Lemma.Algebra.Mul_Sub.eq.SubMulS
import Lemma.Algebra.EqMul_Div.of.Ne_0
open Algebra


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : a > 0)
  (h₁ : ∀ x : ℝ, a * x² + b * x + c ≥ 0) :
-- imply
  b² - 4 * a * c ≤ 0 := by
-- proof
  have := h₁ (-b / (2 * a))
  rw [DivNeg.eq.NegDiv] at this
  rw [SquareNeg.eq.Square] at this
  rw [SquareDiv.eq.DivSquareS] at this
  rw [SquareMul.eq.MulSquareS] at this
  norm_num at this
  rw [Square.eq.Mul (x := a)] at this
  rw [Mul_Mul.eq.MulMul] at this
  rw [Mul_Div.eq.DivMul] at this
  rw [Mul.comm] at this
  have h_Ne := Ne.of.Gt h₀
  rw [DivMulS.eq.Div.of.Ne_0 h_Ne] at this
  rw [Add_Neg.eq.Sub] at this
  rw [Mul_Div.eq.DivMul] at this
  rw [Mul.eq.Square] at this
  rw [SubDivS.eq.DivMul_Sub.of.Ne_0.Ne_0 (by simp [h_Ne] : 4 * a ≠ 0) (by simp [h_Ne] : 2 * a ≠ 0)] at this
  rw [SubMulS.eq.MulSub] at this
  norm_num at this
  rw [NegMul.eq.MulNeg] at this
  rw [DivMulS.eq.Div.of.Ne_0 (by simp [h_Ne] : 2 * a ≠ 0)] at this
  rw [DivNeg.eq.NegDiv] at this
  rw [AddNeg.eq.Sub] at this
  have := LeMulS.of.Gt_0.Le (by simp [h₀] : 4 * a > 0) this
  norm_num at this
  rw [Mul_Sub.eq.SubMulS] at this
  rw [EqMul_Div.of.Ne_0 (by simp [h_Ne] : 4 * a ≠ 0)] at this
  simp_all


-- created on 2025-04-06
