import Axiom.Algebra.FMod.le.Zero.of.Lt_0
import Axiom.Algebra.Lt.of.Le.Ne
import Axiom.Algebra.Le_Sub_1.of.Lt
import Axiom.Algebra.Sign.eq.Neg1.of.Lt_0
import Axiom.Set.Mem_Icc.of.Le.Le
import Axiom.Algebra.FMod.eq.Sub_MulFDiv
import Axiom.Algebra.FDiv.eq.FloorDiv
import Axiom.Algebra.Le_Sub.of.LeAdd
import Axiom.Algebra.Add.comm
import Axiom.Algebra.LeAdd.of.Le_Sub
import Axiom.Algebra.LtCoeS.of.Lt
import Axiom.Algebra.Le.of.LeCoeS
import Axiom.Algebra.Le.of.GeDivS.Lt_0
import Axiom.Algebra.CoeSub.eq.SubCoeS
import Axiom.Algebra.DivSub.eq.SubDivS
import Axiom.Algebra.Div.eq.One.of.Lt_0
import Axiom.Algebra.CoeMul.eq.MulCoeS
import Axiom.Algebra.Ne.of.Lt
import Axiom.Algebra.EqDivMul.of.Ne_0
import Axiom.Set.Lt.of.Mem_Ico
import Axiom.Set.Mem_IcoFloor
open Algebra Set


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : n.fmod d ≠ 0)
  (h₁ : d < 0) :
-- imply
  n.fmod d ∈ Icc d (sign d) := by
-- proof
  apply Mem_Icc.of.Le.Le
  ·
    rw [FMod.eq.Sub_MulFDiv]
    rw [FDiv.eq.FloorDiv]
    apply Le_Sub.of.LeAdd
    rw [Add.comm]
    apply LeAdd.of.Le_Sub
    have h₁ := LtCoeS.of.Lt.int (R := ℚ) h₁
    apply Le.of.LeCoeS.int (R := ℚ)
    apply Le.of.GeDivS.Lt_0 (h₁ := h₁)
    rw [CoeSub.eq.SubCoeS.int]
    rw [DivSub.eq.SubDivS]
    rw [Div.eq.One.of.Lt_0 h₁]
    rw [CoeMul.eq.MulCoeS]
    have h_Ne := Ne.of.Lt h₁
    rw [EqDivMul.of.Ne_0 h_Ne]
    have := Mem_IcoFloor (x := (n : ℚ) / d)
    have := Lt.of.Mem_Ico this
    linarith
  ·
    have := FMod.le.Zero.of.Lt_0 h₁ n
    have := Lt.of.Le.Ne this h₀
    have := Le_Sub_1.of.Lt this
    simp at this
    have h_Eq := Sign.eq.Neg1.of.Lt_0 h₁
    rw [← h_Eq] at this
    assumption


-- created on 2025-03-30
-- updated on 2025-05-04
