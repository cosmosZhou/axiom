import Lemma.Algebra.Lt.of.LtSquareS.Ge_0
import Lemma.Algebra.Mul.ge.Zero.of.Ge_0.Ge_0
import Lemma.Algebra.Sqrt.ge.Zero
import Lemma.Algebra.SquareAdd.eq.AddAddSquareS_MulMul2
import Lemma.Algebra.SquareMul.eq.MulSquareS
import Lemma.Algebra.EqSquareSqrt.of.Ge_0
import Lemma.Algebra.Div.ge.Zero.of.Ge_0.Gt_0
import Lemma.Algebra.Mul_Add.eq.AddMulS
import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.DivMul.eq.MulDiv
import Lemma.Algebra.LtAdd.of.Lt_Sub
import Lemma.Algebra.Lt.of.Sub.gt.Zero
import Lemma.Algebra.Add.comm
import Lemma.Algebra.SubAdd.eq.Add_Sub
import Lemma.Algebra.SquareSub.eq.SubAddSquareS_MulMul2
import Lemma.Algebra.GtSqrtS.of.Gt.Gt_0
import Lemma.Algebra.Sub.gt.Zero.of.Gt
import Lemma.Algebra.Square.gt.Zero.of.Gt_0
import Lemma.Algebra.Mul.comm
import Lemma.Algebra.EqSquareSqrt.of.Gt_0
import Lemma.Algebra.SubAdd.eq.AddSub
import Lemma.Algebra.AddSub_Mul2Sqrt.gt.Zero.of.Gt_1
open Algebra


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 1) :
-- imply
  1 + √x < 2 * √((x + 1) / 2) := by
-- proof
  apply Lt.of.LtSquareS.Ge_0
  ·
    rw [SquareMul.eq.MulSquareS]
    rw [EqSquareSqrt.of.Ge_0]
    ·
      rw [SquareAdd.eq.AddAddSquareS_MulMul2]
      norm_num
      field_simp
      rw [Mul_Add.eq.AddMulS]
      rw [DivAdd.eq.AddDivS]
      rw [DivMul.eq.MulDiv]
      norm_num
      apply LtAdd.of.Lt_Sub
      apply LtAdd.of.Lt_Sub
      ring_nf
      apply Lt.of.Sub.gt.Zero
      rw [Add.comm]
      rw [SubAdd.eq.Add_Sub]
      norm_num
      rw [Mul.comm]
      apply AddSub_Mul2Sqrt.gt.Zero.of.Gt_1 h
    ·
      apply Div.ge.Zero.of.Ge_0.Gt_0
      ·
        linarith [h]
      ·
        norm_num
  ·
    apply Mul.ge.Zero.of.Ge_0.Ge_0
    ·
      norm_num
    ·
      apply Sqrt.ge.Zero


-- created on 2025-04-06
