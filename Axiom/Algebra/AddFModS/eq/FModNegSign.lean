import sympy.core.relational
import Axiom.Logic.Ne.of.NotEq
import Axiom.Algebra.FModNeg.eq.Ite_0Sub_FMod
import Axiom.Algebra.FModNeg.eq.Zero.of.FMod.eq.Zero
import Axiom.Algebra.FModSub.eq.FModNeg.of.FMod.eq.Zero
import Axiom.Algebra.Any_Eq_AddMul.of.EqFMod
import Axiom.Algebra.SubAdd.eq.Add_Sub
import Axiom.Algebra.FModAddMul.eq.FMod
import Axiom.Algebra.FModNegSign.eq.Sub_Sign
import Axiom.Algebra.AddSub.eq.Sub_Sub
import Axiom.Algebra.EqSub.of.Eq_Add
import Axiom.Algebra.Add.comm
import Axiom.Algebra.Eq_Add.of.EqSub
import Axiom.Algebra.EqFMod.of.Mul_Add_Sign.lt.Zero
import Axiom.Algebra.SubSub.eq.Sub_Add
import Axiom.Algebra.LeSign.of.Gt_0
import Axiom.Set.MulSubS.le.Zero.of.Mem_Icc
import Axiom.Algebra.Mul.comm
import Axiom.Algebra.Lt.of.Le.Ne
import Axiom.Algebra.Le.of.NotGt
import Axiom.Set.FMod.in.IccSign.of.FMod.ne.Zero.Gt_0
import Axiom.Set.FMod.in.Icc_Sign.of.FMod.ne.Zero.Lt_0
open Algebra Set Logic


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  (-n).fmod d + (n - sign d).fmod d = (-sign d).fmod d := by
-- proof
  by_cases h_d : d = 0
  ·
    rw [h_d]
    norm_num
  ·
    have h_d := Ne.of.NotEq h_d
    have h_Ite := FModNeg.eq.Ite_0Sub_FMod (n := n) (d := d)
    by_cases h_nd : n.fmod d = 0
    ·
      simp [h_nd] at h_Ite
      rw [h_Ite]
      simp
      have := FModNeg.eq.Zero.of.FMod.eq.Zero h_Ite
      rw [EqNegNeg] at this
      apply FModSub.eq.FModNeg.of.FMod.eq.Zero this
    ·
      simp [h_nd] at h_Ite
      have h_nd := Ne.of.NotEq h_nd
      rw [h_Ite]
      denote h_r : r = n.fmod d
      rw [← h_r]
      have := Any_Eq_AddMul.of.EqFMod h_r.symm
      let ⟨q, h_n⟩ := this
      rw [h_n]
      rw [SubAdd.eq.Add_Sub]
      rw [FModAddMul.eq.FMod]
      rw [FModNegSign.eq.Sub_Sign]
      rw [AddSub.eq.Sub_Sub]
      simp
      apply EqSub.of.Eq_Add
      rw [Add.comm]
      apply Eq_Add.of.EqSub
      apply Eq.symm
      apply EqFMod.of.Mul_Add_Sign.lt.Zero
      rw [SubSub.eq.Sub_Add]
      rw [AddSub.eq.Sub_Sub]
      rw [EqSubAdd.int true]
      by_cases h_d' : d > 0
      ·
        apply MulSubS.le.Zero.of.Mem_Icc
  --       have := LeSign.of.Gt_0 h_d'
        have := FMod.in.IccSign.of.FMod.ne.Zero.Gt_0 h_nd h_d'
        assumption
      ·
        have h_d' := Le.of.NotGt h_d'
        have h_d' := Lt.of.Le.Ne h_d' h_d
        rw [Mul.comm]
        apply MulSubS.le.Zero.of.Mem_Icc
        have := FMod.in.Icc_Sign.of.FMod.ne.Zero.Lt_0 h_nd h_d'
        assumption


-- created on 2025-03-30
