import Axiom.Algebra.FMod.ge.Zero.of.Gt_0
import Axiom.Algebra.Gt.of.Ge.Ne
import Axiom.Algebra.Ge_Add_1.of.Gt
import Axiom.Algebra.Sign.eq.One.of.Gt_0
import Axiom.Set.Mem_Icc.of.Le.Le
import Axiom.Algebra.FMod.eq.Sub_MulFDiv
import Axiom.Algebra.FDiv.eq.FloorDiv
import Axiom.Algebra.LeSub.of.Le_Add
import Axiom.Algebra.Add.comm
import Axiom.Algebra.Le_Add.of.LeSub
import Axiom.Algebra.Le.of.LeDivS.Gt_0
import Axiom.Algebra.GtCoeS.of.Gt
import Axiom.Algebra.Le.of.LeCoeS
import Axiom.Algebra.CoeSub.eq.SubCoeS
import Axiom.Algebra.DivSub.eq.SubDivS
import Axiom.Algebra.Div.eq.One.of.Gt_0
import Axiom.Algebra.CoeMul.eq.MulCoeS
import Axiom.Algebra.EqDivMul.of.Ne_0
import Axiom.Algebra.Ne.of.Gt
import Axiom.Set.Mem_IcoFloor
import Axiom.Set.Lt.of.Mem_Ico
open Algebra Set


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : n.fmod d ≠ 0)
  (h₁ : d > 0) :
-- imply
  n.fmod d ∈ Icc (sign d) d := by
-- proof
  apply Mem_Icc.of.Le.Le
  ·
    have := FMod.ge.Zero.of.Gt_0 h₁ n
    have := Gt.of.Ge.Ne this h₀
    have := Ge_Add_1.of.Gt this
    simp at this
    have h_Eq := Sign.eq.One.of.Gt_0 h₁
    rw [← h_Eq] at this
    assumption
  ·
    rw [FMod.eq.Sub_MulFDiv]
    rw [FDiv.eq.FloorDiv]
    apply LeSub.of.Le_Add
    rw [Add.comm]
    apply Le_Add.of.LeSub
    have h₁ := GtCoeS.of.Gt.int (R := ℚ) h₁
    apply Le.of.LeCoeS.int (R := ℚ)
    apply Le.of.LeDivS.Gt_0 (h₁ := h₁)
    rw [CoeSub.eq.SubCoeS.int]
    rw [DivSub.eq.SubDivS]
    rw [Div.eq.One.of.Gt_0 h₁]
    rw [CoeMul.eq.MulCoeS]
    have h_Ne := Ne.of.Gt h₁
    rw [EqDivMul.of.Ne_0 h_Ne]
    have := Mem_IcoFloor (x := (n : ℚ) / d)
    have := Lt.of.Mem_Ico this
    linarith


-- created on 2025-03-30
-- updated on 2025-05-04
