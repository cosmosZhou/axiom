import Axiom.sympy.core.numbers
import Axiom.Algebra.SquareSub.eq.Sub_.AddSquareS.MulMul2
import Axiom.Algebra.Mul_Sub.eq.SubMulS
import Axiom.Algebra.Eq_.Add.Zero.to.Eq_Neg
import Axiom.Algebra.Add_Sub.eq.SubAdd
import Axiom.Algebra.Mul_Div.eq.DivMul
import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Mul_Mul.eq.MulMul
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.DivMul.eq.MulDiv

import Axiom.Algebra.SquareDiv.eq.DivSquareS
import Axiom.Algebra.SquareMul.eq.MulSquareS
import Axiom.Algebra.Ne_0.to.Eq_.Div_Square.Inv

import Axiom.Algebra.Mul_Inv.eq.Div
import Axiom.Algebra.SubAdd.eq.Add_Sub

import Axiom.Algebra.Ne_0.Ne_0.to.Eq_.SubDivS.Mul_Div_.Sub.Mul
import Axiom.Algebra.DivNeg.eq.NegDiv
import Axiom.Algebra.EqSub.to.Eq_Add

import Axiom.Algebra.DivAdd.eq.AddDivS
import Axiom.Algebra.MulNeg.eq.NegMul
import Axiom.Algebra.Mul_Neg.eq.NegMul
import Axiom.Algebra.Add_Neg.eq.Sub

namespace Algebra.Ne_0.Eq_.Add_.Mul_Square.Mul.Zero.to.Or_Eq_Div_.Sub_Sqrt


theorem Mul2
  {x a b c : ℂ}
-- given
  (h0 : a ≠ 0)
  (h1 : a * x ^ 2 + b * x + c = 0) :
-- imply
  let δ : ℂ := b ^ 2 - 4 * a * c
  x = (-b + √δ) / (2 * a) ∨
  x = (-b - √δ) / (2 * a) := by
-- proof
  let δ : ℂ := b ^ 2 - 4 * a * c
  let x' := x + b / (2 * a)

  have h2 : x = x' - b / (2 * a) := by simp [x']

  rw [h2] at h1

  rw [
    SquareSub.eq.Sub_.AddSquareS.MulMul2,
    Mul_Sub.eq.SubMulS,
    Mul_Add.eq.AddMulS,
    Mul_Sub.eq.SubMulS
  ] at h1

  have h1 := Eq_.Add.Zero.to.Eq_Neg h1
  rw [Add_Sub.eq.SubAdd] at h1
  rw [Mul_Div.eq.DivMul] at h1
  rw [Mul_Div.eq.DivMul] at h1
  rw [Mul_Div.eq.DivMul] at h1
  rw [Mul.eq.Square] at h1
  rw [Mul_Mul.eq.MulMul] at h1
  rw [Mul_Mul.eq.MulMul] at h1
  rw [Mul.comm (a := a) (b := 2)] at h1
  rw [DivMul.eq.MulDiv] at h1

  have h2 : 2 * a ≠ 0 := by simp [h0]

  simp [h2] at h1

  rw [Mul.comm (b := b)] at h1

  simp at h1

  rw [SquareDiv.eq.DivSquareS] at h1
  rw [Mul_Div.eq.DivMul] at h1
  rw [Mul.comm (b := b ^ 2)] at h1
  rw [SquareMul.eq.MulSquareS] at h1
  rw [Div_Mul.eq.DivDiv] at h1
  rw [DivMul.eq.MulDiv] at h1
  rw [DivMul.eq.Mul_Div] at h1
  rw [Ne_0.to.Eq_.Div_Square.Inv] at h1
  rw [show (2:ℂ) ^ 2 = 4 by norm_num] at h1
  rw [Mul_Inv.eq.Div] at h1
  rw [DivDiv.eq.Div_Mul] at h1
  rw [SubAdd.eq.Add_Sub] at h1

  have h4 : 4 * a ≠ 0 := by simp [h0]
  rw [Ne_0.Ne_0.to.Eq_.SubDivS.Mul_Div_.Sub.Mul h4 h2] at h1
  rw [SubMulS.eq.MulSub] at h1

  rw [show (2:ℂ) - 4 = -2 by norm_num] at h1
  rw [MulNeg.eq.NegMul] at h1
  rw [DivNeg.eq.NegDiv] at h1
  rw [Mul_Neg.eq.NegMul] at h1
  rw [Add_Neg.eq.Sub] at h1

  rw [Ne_0.to.Eq_.Div_Mul.Inv h2 true] at h1

  rw [Mul_Inv.eq.Div] at h1

  have h1 := EqSub.to.Eq_Add h1
  have h_δ : δ = b ^ 2 - 4 * a * c := by simp
  have h_δ := EqSub.to.Eq_Add h_δ.symm

  rw [h_δ] at h1

  rw [DivAdd.eq.AddDivS] at h1
  simp [h4] at h1

  sorry


end Algebra.Ne_0.Eq_.Add_.Mul_Square.Mul.Zero.to.Or_Eq_Div_.Sub_Sqrt

-- created on 2024-07-01
