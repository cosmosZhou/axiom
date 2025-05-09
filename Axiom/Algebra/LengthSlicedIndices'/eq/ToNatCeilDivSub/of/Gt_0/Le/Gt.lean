import stdlib.List
import Axiom.Algebra.Sub.gt.Zero.of.Gt
import Axiom.Algebra.GtCoeS.of.Gt
import Axiom.Algebra.CoeSub.eq.SubCoeS.of.Gt
import Axiom.Algebra.GtDivS.of.Gt.Gt_0
import Axiom.Algebra.GeCeil
import Axiom.Algebra.Gt.of.Ge.Gt
import Axiom.Algebra.Gt.of.GtCoeS
import Axiom.Algebra.Eq_ToNat.of.Gt_0
import Axiom.Algebra.LeMulS.of.Le.Gt_0
import Axiom.Algebra.EqMulDiv.of.Gt_0
import Axiom.Algebra.SubCoeS.eq.CoeSub.of.Gt
import Axiom.Algebra.Eq.of.EqCoeS
import Axiom.Algebra.LengthSlicedIndices'.eq.CeilDivSub.of.Gt_0.Le.Gt.Sub.le.Mul
open Algebra


@[main]
private lemma main
-- given
  (h_stop : start > stop)
  (h_start : start ≤ n)
  (h_step : step > 0) :
-- imply
  (Nat.sliced_indices' h_stop h_start h_step).length = ⌈(start - stop : ℚ) / step⌉.toNat := by
-- proof
  have h_Gt_0 := Sub.gt.Zero.of.Gt.nat h_stop
  have h_Gt_0 := GtCoeS.of.Gt.nat (R := ℚ) h_Gt_0
  rw [CoeSub.eq.SubCoeS.of.Gt h_stop] at h_Gt_0
  have h_step' := GtCoeS.of.Gt.nat (R := ℚ) h_step
  have h_Gt_0 := GtDivS.of.Gt.Gt_0 h_Gt_0 h_step'
  simp at h_Gt_0
  have h_Le := GeCeil (x := (start - stop : ℚ) / step)
  have h_Gt_0 := Gt.of.Ge.Gt h_Le h_Gt_0
  have h_Gt_0 := Gt.of.GtCoeS.int h_Gt_0
  have h_Eq := Eq_ToNat.of.Gt_0 h_Gt_0
  apply Eq.of.EqCoeS.nat (R := ℤ)
  rw [← h_Eq]
  have h_Le := LeMulS.of.Le.Gt_0 h_Le h_step'
  rw [EqMulDiv.of.Gt_0 h_step'] at h_Le
  rw [h_Eq] at h_Le
  rw [SubCoeS.eq.CoeSub.of.Gt h_stop] at h_Le
  have h_Le : start - stop ≤ ⌈((start - stop : ℕ) : ℚ) / step⌉.toNat * step := by 
    norm_cast
    norm_cast at h_Le
  apply LengthSlicedIndices'.eq.CeilDivSub.of.Gt_0.Le.Gt.Sub.le.Mul h_Le h_stop h_start h_step


-- created on 2025-05-04
-- updated on 2025-05-05
