import Axiom.Algebra.MulAdd.eq.AddMulS
import Axiom.Algebra.Mul_Add.eq.AddMulS
import Axiom.Algebra.Eq.Eq.to.EqMulS
import Axiom.Algebra.Sub.eq.NegSub
import Axiom.Algebra.Mul_Div.eq.DivMul
import Axiom.Algebra.Eq.to.EqSubS
import Axiom.Algebra.MulDiv.eq.DivMul
import Axiom.Algebra.Ne_0.Ne_0.to.SubDivS.eq.Div_.SubMulS.Mul
import Axiom.Algebra.Mul_Neg.eq.NegSquare
import Axiom.Algebra.DivDiv.eq.Div_Mul
import Axiom.Algebra.Mul_Mul.eq.MulMul
import Axiom.Algebra.MulMul.comm
import Axiom.Algebra.Gt.Gt_0.to.GtMulS
import Axiom.Algebra.Mul0.eq.Zero
import Axiom.Algebra.NegSquare.le.Zero
import Axiom.Algebra.Mul.gt.Zero.to.Add.ne.Zero
import Axiom.Algebra.Ne_0.to.Square.gt.Zero
import Axiom.Algebra.Le.Gt_0.to.LeDivS
import Axiom.Algebra.Mul.gt.Zero.to.Ne_0

namespace Algebra.Mul.gt.Zero.to.MulSubS_Div.le

theorem Zero
-- R is a linear ordered field, e.g. ℝ or ℚ
  [LinearOrderedField R]
-- TP denotes true positives
-- TN denotes true negatives
-- P denotes positives
-- N denotes negatives
-- A denotes accuracy
  {TP TN P N : R}
-- given
  (h₀ : P * N > 0) :
-- imply
  let A := (TP + TN) / (P + N)
  (A - TP / P) * (A - TN / N) ≤ 0 := by
-- proof
  have h_Add_ne_Zero := Mul.gt.Zero.to.Add.ne.Zero h₀

  let A := (TP + TN) / (P + N)
  have h_A : A = (TP + TN) / (P + N) := rfl
  have h₁ := Eq.to.EqSubS h_A (TP / P)

  have h_together := Ne_0.Ne_0.to.SubDivS.eq.Div_.SubMulS.Mul
    h_Add_ne_Zero
    (Mul.gt.Zero.to.Ne_0 h₀)
    (x := TP + TN)
    (y := TP)
  have h₁ := Eq.trans h₁ h_together
  rw [
    MulAdd.eq.AddMulS,
    Mul_Add.eq.AddMulS
  ] at h₁

  simp at h₁

  have h₂ := Eq.to.EqSubS h_A (TN / N)
  have h_together := Ne_0.Ne_0.to.SubDivS.eq.Div_.SubMulS.Mul
    h_Add_ne_Zero
    (Mul.gt.Zero.to.Ne_0 h₀ false)
    (x := TP + TN)
    (y := TN)

  have h₂ := Eq.trans h₂ h_together
  rw [
    MulAdd.eq.AddMulS,
    Mul_Add.eq.AddMulS
  ] at h₂

  simp at h₂
  rw [Sub.eq.NegSub (a := TP * N)] at h₂

  have h := Eq.Eq.to.EqMulS h₁ h₂
  rw [Mul_Div.eq.DivMul] at h
  rw [MulDiv.eq.DivMul] at h

  rw [Mul_Neg.eq.NegSquare] at h

  rw [DivDiv.eq.Div_Mul] at h
  rw [Mul_Mul.eq.MulMul] at h
  rw [MulMul.comm (a := P + N)] at h
  rw [Mul.eq.Square] at h
  rw [MulMul.eq.Mul_Mul] at h

  have h_gt_Zero := Gt.Gt_0.to.GtMulS
    (Ne_0.to.Square.gt.Zero h_Add_ne_Zero)
    h₀
  simp only [Mul0.eq.Zero] at h_gt_Zero
  have h_le_Zero := NegSquare.le.Zero (a := TN * P - TP * N)
  have h_le_Zero := Le.Gt_0.to.LeDivS h_le_Zero h_gt_Zero
  simp at h_le_Zero
  rw [← h] at h_le_Zero
  exact h_le_Zero


end Algebra.Mul.gt.Zero.to.MulSubS_Div.le

-- created on 2024-11-29
