import Lemma.Algebra.Add.eq.Mul2
import Lemma.Algebra.Add.comm
import Lemma.Algebra.Mul.comm
import Lemma.Algebra.AddAdd.comm
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Algebra.AddMulS.eq.Mul_Add
import Lemma.Algebra.Div_Mul.eq.DivDiv
import Lemma.Algebra.GtMulS.of.Gt.Gt_0
import Lemma.Algebra.AddDivS.eq.DivAdd
open Algebra


@[main]
private lemma main
-- α is a linear ordered field, e.g. ℝ or ℚ
  [LinearOrderedField α]
-- TP denotes true positive
-- FP denotes false positive
-- TN denotes true negative
-- FN denotes false negative
  {TP FP TN FN : α}
-- given
-- the sum of Positive equals the sum of Negative
  (h₀ : TP + FP = TN + FN)
  (h₁ : (TP + TN) / (TP + FP + TN + FN) > 1 / 2) :
-- imply
  TP / (TP + FP) + TN / (TN + FN) > 1 := by
-- proof
  rw [h₀] at h₁
  rw [Add.comm (a := TN)] at h₁
  rw [AddAdd.eq.Add_Add (a := FN) (b := TN)] at h₁
  simp only [Add.eq.Mul2] at h₁
  rw [AddAdd.comm] at h₁
  simp only [Add.eq.Mul2] at h₁
  rw [AddMulS.eq.Mul_Add] at h₁
  rw [Mul.comm] at h₁
  rw [Div_Mul.eq.DivDiv] at h₁
  have h₁ := GtMulS.of.Gt.Gt_0 h₁ (by norm_num : (2 : α) > 0)
  simp at h₁
  rw [h₀]
  rw [AddDivS.eq.DivAdd]
  rw [Add.comm (a := TN)]
  exact h₁


-- created on 2024-11-28
