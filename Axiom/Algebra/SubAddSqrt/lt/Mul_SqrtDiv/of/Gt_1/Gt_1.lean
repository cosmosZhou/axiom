import Axiom.Algebra.Lt.of.LtSquareS.Ge_0
import Axiom.Algebra.Mul.ge.Zero.of.Ge_0.Ge_0
import Axiom.Algebra.Sqrt.ge.Zero
import Axiom.Algebra.SquareMul.eq.MulSquareS
import Axiom.Algebra.EqSquareSqrt.of.Ge_0
import Axiom.Algebra.Div.ge.Zero.of.Ge_0.Gt_0
import Axiom.Algebra.SquareAdd.eq.AddAddSquareS_MulMul2
import Axiom.Algebra.SubAdd.eq.Add_Sub
import Axiom.Algebra.DivMul.eq.MulDiv
import Axiom.Algebra.EqDivSquare
import Axiom.Algebra.Mul_Add.eq.AddMulS
import Axiom.Algebra.Lt.of.Sub.gt.Zero
import Axiom.Algebra.SubAdd.eq.AddSub
import Axiom.Algebra.Sub_Add.eq.SubSub
import Axiom.Algebra.SubMul.eq.MulSub_1
import Axiom.Algebra.SubSub.comm
import Axiom.Algebra.AddSub.eq.Add_Sub
import Axiom.Algebra.SubMulS.eq.MulSub
import Axiom.Algebra.Square.eq.Mul
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.AddMulS.eq.MulAdd
import Axiom.Algebra.EqSub_Sub
import Axiom.Algebra.Mul.gt.Zero.of.Gt_0.Gt_0
import Axiom.Algebra.AddSub_Mul2Sqrt.gt.Zero.of.Gt_1
open Algebra


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ}
-- given
  (h₀ : n > 1)
  (h₁ : x > 1) :
-- imply
  √x + n - 1 < n * √((x + n - 1) / n) := by
-- proof
  apply Lt.of.LtSquareS.Ge_0
  ·
    rw [SquareMul.eq.MulSquareS]
    rw [EqSquareSqrt.of.Ge_0]
    ·
      rw [SubAdd.eq.Add_Sub]
      rw [SquareAdd.eq.AddAddSquareS_MulMul2]
      field_simp
      rw [DivMul.eq.MulDiv]
      rw [EqDivSquare]
      rw [SubAdd.eq.Add_Sub]
      rw [Mul_Add.eq.AddMulS]
      apply Lt.of.Sub.gt.Zero
      rw [SubAdd.eq.AddSub]
      rw [Sub_Add.eq.SubSub]
      rw [Sub_Add.eq.SubSub]
      rw [SubMul.eq.MulSub_1]
      rw [SubSub.comm]
      rw [AddSub.eq.Add_Sub]
      rw [Square.eq.Mul]
      rw [SubMulS.eq.MulSub]
      rw [EqSub_Sub]
      rw [Mul.comm]
      rw [SubMulS.eq.MulSub]
      rw [AddMulS.eq.MulAdd]
      apply Mul.gt.Zero.of.Gt_0.Gt_0
      ·
        apply AddSub_Mul2Sqrt.gt.Zero.of.Gt_1 h₁
      ·
        simp
        linarith [h₀]
    ·
      apply Div.ge.Zero.of.Ge_0.Gt_0
      ·
        linarith [h₀]
      ·
        norm_cast
        linarith [h₀]
  ·
    apply Mul.ge.Zero.of.Ge_0.Ge_0
    ·
      simp
    ·
      apply Sqrt.ge.Zero


-- created on 2025-04-06
