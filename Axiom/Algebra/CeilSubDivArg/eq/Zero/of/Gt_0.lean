import Axiom.Set.Arg.mem.IocNegPiPi
import Axiom.Set.MemDiv.of.Mem_Ioc.Gt_0
import Axiom.Set.MemSub.of.Mem_Ioc
import Axiom.Algebra.DivSub.eq.SubDivS
import Axiom.Algebra.Div_Mul.eq.Inv.of.Ne_0
import Axiom.Algebra.DivNeg.eq.NegDiv
import Axiom.Algebra.Inv.eq.Div1
import Axiom.Algebra.DivDiv.eq.Div_Mul
import Axiom.Algebra.Mul_Mul.eq.MulMul
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.Pi.gt.Zero
import Axiom.Algebra.Mul.gt.Zero.of.Gt_0.Gt_0
import Axiom.Algebra.Pi.ne.Zero
import Axiom.Set.Ceil.eq.Zero.of.Mem_Ioc
import Axiom.Set.Mem.of.Mem.Subset
import Axiom.Set.SubsetIocS.of.Le.Ge
import Axiom.Algebra.Le_Sub.of.LeAdd
import Axiom.Algebra.Inv.le.One.of.Gt_0
import Axiom.Algebra.Ge_Sub.of.GeAdd
open Set Algebra


@[main]
private lemma main
  {z : ℂ}
  {n : ℕ}
-- given
  (h : n > 0) :
-- imply
  ⌈arg z / (2 * n * π) - 1 / 2⌉ = 0 := by
-- proof
  have h_mem := Arg.mem.IocNegPiPi z
  have h_mem := MemDiv.of.Mem_Ioc.Gt_0 h_mem (by apply Nat.cast_pos.mpr h : (n : ℝ) > 0)
  have h_mem := MemSub.of.Mem_Ioc h_mem π
  have h_Gt_0 := Mul.gt.Zero.of.Gt_0.Gt_0 (by norm_num : (2 : ℝ) > 0) Pi.gt.Zero
  have h_mem := MemDiv.of.Mem_Ioc.Gt_0 h_mem h_Gt_0
  simp only [DivSub.eq.SubDivS] at h_mem
  simp only [DivDiv.eq.Div_Mul] at h_mem
  rw [DivNeg.eq.NegDiv] at h_mem
  simp only [Mul_Mul.eq.MulMul] at h_mem
  simp only [Div_Mul.eq.Inv.of.Ne_0 Pi.ne.Zero true] at h_mem
  simp only [Inv.eq.Div1] at h_mem
  simp only [Mul.comm (b := (2 : ℝ))] at h_mem
  apply Ceil.eq.Zero.of.Mem_Ioc
  apply Mem.of.Mem.Subset h_mem
  have := Inv.le.One.of.Gt_0 h
  apply SubsetIocS.of.Le.Ge
  apply Le_Sub.of.LeAdd
  norm_num
  assumption
  apply Ge_Sub.of.GeAdd
  norm_num
  assumption


-- created on 2025-03-02
