import Axiom.Algebra.Mul_Div.eq.DivMul
import Axiom.Algebra.Gt_0.Gt.to.GtMulS
import Axiom.Algebra.Gt.Gt_0.to.GtDivS
import Axiom.Algebra.Gt_0.to.Div.eq.One
import Axiom.Algebra.Gt_0.Gt_0.to.Mul.gt.Zero
import Axiom.Algebra.Gt_0.Gt_0.to.Add.gt.Zero
import Axiom.Algebra.Lt.to.Sub.gt.Zero
import Axiom.Algebra.GtAdd.to.Gt_Sub
import Axiom.Algebra.GtSub.to.Gt_Add
import Axiom.Algebra.MulSub.eq.SubMulS
import Axiom.Algebra.Mul1.simp
import Axiom.Algebra.Mul_1.simp
import Axiom.Algebra.Add.comm

namespace Algebra.And.And.Add.gt.One.to.GtDiv_.Mul.Add_.Mul.MulSubS1

-- prerequisite of data sifting using a reward model
theorem sift
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

  have h := GtAdd.to.Gt_Sub h
  have h_Sub_gt_0 := Lt.to.Sub.gt.Zero hₚ.right
  have h := Gt_0.Gt.to.GtMulS h_Sub_gt_0 h

  rw [MulSub.eq.SubMulS] at h
  simp only [Mul1.simp] at h
  have h_Gt := GtSub.to.Gt_Add h
  rw [Add.comm] at h_Gt

  have h_Add_gt_0 := Gt_0.Gt_0.to.Add.gt.Zero
    (Gt_0.Gt_0.to.Mul.gt.Zero hₚ.left hₜ.left)
    (Gt_0.Gt_0.to.Mul.gt.Zero
      h_Sub_gt_0
      (Lt.to.Sub.gt.Zero hₜ.right)
    )

  have h_Gt_1 := Gt.Gt_0.to.GtDivS h_Gt h_Add_gt_0
  simp only [Gt_0.to.Div.eq.One h_Add_gt_0] at h_Gt_1

  have h_Gt := Gt_0.Gt.to.GtMulS hₚ.left h_Gt_1

  rw [Mul_1.simp] at h_Gt
  rw [Mul_Div.eq.DivMul] at h_Gt
  exact h_Gt


end Algebra.And.And.Add.gt.One.to.GtDiv_.Mul.Add_.Mul.MulSubS1

-- created on 2024-11-25
