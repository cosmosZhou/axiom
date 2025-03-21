import Axiom.Algebra.SquareSub.eq.SubAddSquareS_MulMul2
import Axiom.Algebra.Mul_Sub.eq.SubMulS
import Axiom.Algebra.Eq_Neg.of.Add.eq.Zero
import Axiom.Algebra.Add_Sub.eq.SubAdd
import Axiom.Algebra.Mul_Div.eq.DivMul
import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Mul_Mul.eq.MulMul
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.DivMul.eq.MulDiv
import Axiom.Algebra.SquareDiv.eq.DivSquareS
import Axiom.Algebra.SquareMul.eq.MulSquareS
import Axiom.Algebra.Eq_Inv_Div_Square.of.Ne_0
import Axiom.Algebra.Mul_Inv.eq.Div
import Axiom.Algebra.SubAdd.eq.Add_Sub
import Axiom.Algebra.Eq_Mul_Div_Mul__Sub__SubDivS.of.Ne_0.Ne_0
import Axiom.Algebra.DivNeg.eq.NegDiv
import Axiom.Algebra.Eq_Add.of.EqSub
import Axiom.Algebra.DivAdd.eq.AddDivS
import Axiom.Algebra.MulNeg.eq.NegMul
import Axiom.Algebra.Mul_Neg.eq.NegMul
import Axiom.Algebra.Add_Neg.eq.Sub
import Axiom.Algebra.Mul_Add.eq.AddMulS
import Axiom.Algebra.Div_Mul.eq.DivDiv
import Axiom.Algebra.DivMul.eq.Mul_Div
import Axiom.Algebra.DivDiv.eq.Div_Mul
import Axiom.Algebra.SubMulS.eq.MulSub
import Axiom.Algebra.Div_Mul.eq.Inv.of.Ne_0
open Algebra


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h₀ : a ≠ 0)
  (h₁ : a * x² + b * x + c = 0) :
-- imply
  let Δ : ℂ := b² - 4 * a * c
  x = (-b + √Δ) / (2 * a) ∨
    x = (-b - √Δ) / (2 * a) := by
-- proof
  let Δ : ℂ := b² - 4 * a * c
  let x' := x + b / (2 * a)
  have h₂ : x = x' - b / (2 * a) := by simp [x']
  rw [h₂] at h₁
  rw [
    SquareSub.eq.SubAddSquareS_MulMul2,
    Mul_Sub.eq.SubMulS,
    Mul_Add.eq.AddMulS,
    Mul_Sub.eq.SubMulS
  ] at h₁
  have h₁ := Eq_Neg.of.Add.eq.Zero h₁
  rw [Add_Sub.eq.SubAdd] at h₁
  rw [Mul_Div.eq.DivMul] at h₁
  rw [Mul_Div.eq.DivMul] at h₁
  rw [Mul_Div.eq.DivMul] at h₁
  rw [Mul.eq.Square] at h₁
  rw [Mul_Mul.eq.MulMul] at h₁
  rw [Mul_Mul.eq.MulMul] at h₁
  rw [Mul.comm (a := a) (b := 2)] at h₁
  rw [DivMul.eq.MulDiv] at h₁
  have h₂ : 2 * a ≠ 0 := by simp [h₀]
  simp [h₂] at h₁
  rw [Mul.comm (b := b)] at h₁
  simp at h₁
  rw [SquareDiv.eq.DivSquareS] at h₁
  rw [Mul_Div.eq.DivMul] at h₁
  rw [Mul.comm (b := b²)] at h₁
  rw [SquareMul.eq.MulSquareS] at h₁
  rw [Div_Mul.eq.DivDiv] at h₁
  rw [DivMul.eq.MulDiv] at h₁
  rw [DivMul.eq.Mul_Div] at h₁
  rw [Eq_Inv_Div_Square.of.Ne_0] at h₁
  rw [show (2 : ℂ)² = 4 by norm_num] at h₁
  rw [Mul_Inv.eq.Div] at h₁
  rw [DivDiv.eq.Div_Mul] at h₁
  rw [SubAdd.eq.Add_Sub] at h₁
  have h₃ : 4 * a ≠ 0 := by simp [h₀]
  rw [Eq_Mul_Div_Mul__Sub__SubDivS.of.Ne_0.Ne_0 h₃ h₂] at h₁
  rw [SubMulS.eq.MulSub] at h₁
  rw [show (2 : ℂ) - 4 = -2 by norm_num] at h₁
  rw [MulNeg.eq.NegMul] at h₁
  rw [DivNeg.eq.NegDiv] at h₁
  rw [Mul_Neg.eq.NegMul] at h₁
  rw [Add_Neg.eq.Sub] at h₁
  rw [Div_Mul.eq.Inv.of.Ne_0 h₂ true] at h₁
  rw [Mul_Inv.eq.Div] at h₁
  have h₁ := Eq_Add.of.EqSub h₁
  have h_Δ : Δ = b² - 4 * a * c := by simp
  have h_Δ := Eq_Add.of.EqSub h_Δ.symm
  rw [h_Δ] at h₁
  rw [DivAdd.eq.AddDivS] at h₁
  simp [h₃] at h₁
  sorry


-- created on 2024-07-01
-- updated on 2025-03-16
