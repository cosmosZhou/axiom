import Axiom.Algebra.Add.eq.Mul2
import Axiom.Algebra.Add.comm
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.AddAdd.comm
import Axiom.Algebra.AddAdd.eq.Add_Add
import Axiom.Algebra.AddMulS.eq.Mul_Add
import Axiom.Algebra.Div_Mul.eq.DivDiv
import Axiom.Algebra.Gt.Gt_0.to.GtMulS
import Axiom.Algebra.AddDivS.eq.DivAdd

namespace Algebra.EqAddS.Div.gt.Half.to.AddDivS.gt

theorem One
-- R is a linear ordered field, e.g. ℝ or ℚ
  [LinearOrderedField R]
-- TP denotes true positive
-- FP denotes false positive
-- TN denotes true negative
-- FN denotes false negative
  {TP FP TN FN : R}
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
  have h₁ := Gt.Gt_0.to.GtMulS h₁ (show 2 > 0 by norm_num)
  simp at h₁
  rw [h₀]
  rw [AddDivS.eq.DivAdd]
  rw [Add.comm (a := TN)]
  exact h₁


end Algebra.EqAddS.Div.gt.Half.to.AddDivS.gt

-- created on 2024-11-28
