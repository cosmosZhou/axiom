import stdlib.List
import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.GeCoeS.of.Ge
import Lemma.Algebra.CoeAdd.eq.AddCoeS
import Lemma.Algebra.CeilDivSub.eq.One.of.GeAdd.Gt_0
import Lemma.Algebra.GtCoeS.of.Gt
import Lemma.Algebra.LeSubS.of.Le
import Lemma.Algebra.DivSub.eq.SubDivS
import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Algebra.CeilSub_1.eq.SubCeil_1
import Lemma.Algebra.SubSub.eq.Sub_Add
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Algebra.Le.of.Sub.eq.Zero
import Lemma.Algebra.MulAdd_1.eq.AddMul
import Lemma.Algebra.EqSubAdd
open Algebra


@[main]
private lemma main
-- given
  (h : stop - start ≤ k * step)
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (h_step : step > 0) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step).length = ⌈(stop - start : ℚ) / step⌉ := by
-- proof
  induction k generalizing start with
  | zero =>
    simp at h
    have h := Le.of.Sub.eq.Zero h
    linarith
  | succ k ih =>
    unfold Nat.sliced_indices
    simp
    split_ifs with h_start'
    ·
      have h' := LeSubS.of.Le.nat h step
      rw [MulAdd_1.eq.AddMul] at h'
      rw [SubSub.eq.Sub_Add.nat] at h'
      rw [EqSubAdd.int false] at h'
      have h_Eq := ih h' h_start'
      rw [h_Eq]
      rw [CoeAdd.eq.AddCoeS.nat]
      rw [Sub_Add.eq.SubSub]
      rw [DivSub.eq.SubDivS]
      rw [Div.eq.One.of.Gt_0 (by simp [h_step])]
      rw [CeilSub_1.eq.SubCeil_1]
      simp
    ·
      simp
      apply Eq.symm
      have h_Ge := Ge.of.NotLt h_start'
      have h_Ge := GeCoeS.of.Ge.nat (R := ℚ) h_Ge
      rw [CoeAdd.eq.AddCoeS.nat] at h_Ge
      apply CeilDivSub.eq.One.of.GeAdd.Gt_0 (by apply GtCoeS.of.Gt.nat h_step) h_Ge (by apply GtCoeS.of.Gt.nat h_start)


-- created on 2025-05-04
