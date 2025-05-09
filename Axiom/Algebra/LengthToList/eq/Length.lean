import stdlib.Slice
import sympy.core.relational
import Axiom.Algebra.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Axiom.Algebra.Eq_Sub.of.Eq_Add
import Axiom.Algebra.LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt
import Axiom.Algebra.ToNatCeil.eq.Zero.of.Le
import Axiom.Algebra.ToNatCeilDivNeg.eq.Zero
import Axiom.Algebra.CoeAdd.eq.AddCoeS
import Axiom.Algebra.ToNat.eq.Zero.of.Le_0
open Algebra


@[main]
private lemma main
  {s : Slice} :
-- imply
  (s.toList n).length = s.length n := by
-- proof
  unfold Slice.toList Slice.length
  match s.step with
  | .ofNat step =>
    simp
    match step with
    | .zero =>
      simp
    | .succ step =>
      simp
      denote h_stop_def : stop = Slice.Add_Mul_DivSub1Sign_2 n s.stop
      denote h_start_def : start = Slice.Add_Mul_DivSub1Sign_2 n s.start
      split_ifs with h_Ge
      ·
        simp
        simp only [
          ← h_stop_def,
          (show (stop.toNat : ℚ) ⊓ (n : ℚ) = stop.toNat.min n by simp),
          (show (step : ℚ) + 1 = step.succ by simp [Nat.succ])
        ]
        have h_Le : stop.toNat.min n ≤ start.toNat := by
          simp_all
        rw [ToNatCeil.eq.Zero.of.Le h_Le]
      ·
        simp only [
          ← h_stop_def,
          (show (stop.toNat : ℚ) ⊓ (n : ℚ) = stop.toNat.min n by simp),
          (show (step : ℚ) + 1 = step.succ by simp [Nat.succ])
        ]
        let start := start.toNat
        let stop := stop.toNat.min n
        let step := step.succ
        have h_start : start < stop := by
          simp_all [start, stop]
        have h_stop : stop ≤ n := by
          simp [stop]
        have h_step : step > 0 := by
          apply Nat.succ_pos
        apply LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt h_start h_stop h_step
  | .negSucc step =>
    simp
    denote h_start_def : start = Slice.Add_Mul_DivSub1Sign_2 n s.start + 1
    denote h_stop_def : stop = Slice.Add_Mul_DivSub1Sign_2 n s.stop + 1
    split_ifs with h_Le
    ·
      simp
      simp only [
        ← h_start_def,
        (show (start.toNat : ℚ) ⊓ (n : ℚ) = start.toNat.min n by simp),
        (show (step : ℚ) + 1 = step.succ by simp [Nat.succ])
      ]
      have h_Le : start.toNat.min n ≤ stop.toNat := by
        simp_all
      rw [ToNatCeil.eq.Zero.of.Le h_Le]
    ·
      simp only [
        ← h_start_def,
        (show (start.toNat : ℚ) ⊓ (n : ℚ) = start.toNat.min n by simp),
        (show (step : ℚ) + 1 = step.succ by simp [Nat.succ])
      ]
      rw [Eq_Sub.of.Eq_Add.left h_start_def] at h_Le
      let start := start.toNat.min n
      let stop := stop.toNat
      let step := step.succ
      have h_start : start ≤ n := by
        simp [start]
      have h_stop : start > stop := by
        simp_all [start, stop]
      have h_step : step > 0 := by
        apply Nat.succ_pos
      apply LengthSlicedIndices'.eq.ToNatCeilDivSub.of.Gt_0.Le.Gt h_stop h_start h_step


-- created on 2025-05-05
