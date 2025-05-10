import Lemma.Algebra.Mul_Div.eq.DivMul
import Lemma.Algebra.GtMulS.of.Gt_0.Gt
import Lemma.Algebra.GtDivS.of.Gt.Gt_0
import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Algebra.Mul.gt.Zero.of.Gt_0.Gt_0
import Lemma.Algebra.Add.gt.Zero.of.Gt_0.Gt_0
import Lemma.Algebra.Sub.gt.Zero.of.Lt
import Lemma.Algebra.Gt_Sub.of.GtAdd
import Lemma.Algebra.Gt_Add.of.GtSub
import Lemma.Algebra.MulSub.eq.SubMulS
import Lemma.Algebra.EqMul1
import Lemma.Algebra.EqMul_1
import Lemma.Algebra.Add.comm
open Algebra


-- prerequisite of data sifting using a reward model
@[main]
private lemma main
-- R is a linear ordered field, e.g. ℝ or ℚ
  [LinearOrderedField R]
-- p, the correctness percentage of the dataset
-- rₜₚ denotes True Positive Rate
-- rₜₙ denotes True Negative Rate
  {p rₜₚ rₜₙ : R}
-- given
  (hₚ : p > 0 ∧ p < 1)
  (hₜ : rₜₚ > 0 ∧ rₜₙ < 1)
  (h : rₜₚ + rₜₙ > 1) :
-- imply
-- after sifting, the correctness percentage of the dataset is bound to be greater than p
  p * rₜₚ / (p * rₜₚ + (1 - p) * (1 - rₜₙ)) > p := by
-- proof
  have h := Gt_Sub.of.GtAdd h
  have h_Sub_gt_0 := Sub.gt.Zero.of.Lt hₚ.right
  have h := GtMulS.of.Gt_0.Gt h_Sub_gt_0 h
  rw [MulSub.eq.SubMulS] at h
  simp only [EqMul1] at h
  have h_Gt := Gt_Add.of.GtSub h
  rw [Add.comm] at h_Gt
  have h_Add_gt_0 := Add.gt.Zero.of.Gt_0.Gt_0
    (Mul.gt.Zero.of.Gt_0.Gt_0 hₚ.left hₜ.left)
    (Mul.gt.Zero.of.Gt_0.Gt_0
      h_Sub_gt_0
      (Sub.gt.Zero.of.Lt hₜ.right)
    )
  have h_Gt_1 := GtDivS.of.Gt.Gt_0 h_Gt h_Add_gt_0
  simp only [Div.eq.One.of.Gt_0 h_Add_gt_0] at h_Gt_1
  have h_Gt := GtMulS.of.Gt_0.Gt hₚ.left h_Gt_1
  rw [EqMul_1] at h_Gt
  rw [Mul_Div.eq.DivMul] at h_Gt
  assumption


-- created on 2024-11-25
