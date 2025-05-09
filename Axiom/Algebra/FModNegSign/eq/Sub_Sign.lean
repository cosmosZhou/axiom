import Axiom.Algebra.Lt.ou.Eq.ou.Gt
import Axiom.Algebra.Sign.eq.Neg1.of.Lt_0
import Axiom.Algebra.Sign.eq.One.of.Gt_0
import Axiom.Algebra.FMod.eq.Sub_MulFDiv
import Axiom.Algebra.Sub.eq.AddNeg
import Axiom.Algebra.EqAddS.of.Eq
import Axiom.Algebra.FDiv1.eq.Neg1.of.Lt_0
import Axiom.Algebra.SubNeg.comm
import Axiom.Algebra.EqSubS.of.Eq
import Axiom.Algebra.FDivNeg1.eq.Neg1.of.Gt_0
open Algebra


@[main]
private lemma main
  {d : ℤ} :
-- imply
  (-sign d).fmod d = d - sign d := by
-- proof
  rcases Lt.ou.Eq.ou.Gt d 0 with h_d | h_d | h_d
  ·
    have := Sign.eq.Neg1.of.Lt_0 h_d
    rw [this]
    simp
    rw [FMod.eq.Sub_MulFDiv]
    rw [Sub.eq.AddNeg]
    apply EqAddS.of.Eq (d := 1)
    rw [FDiv1.eq.Neg1.of.Lt_0 h_d]
    simp
  ·
    rw [h_d]
    norm_num
  ·
    have := Sign.eq.One.of.Gt_0 h_d
    rw [this]
    rw [FMod.eq.Sub_MulFDiv]
    rw [SubNeg.comm]
    apply EqSubS.of.Eq (d := 1)
    rw [FDivNeg1.eq.Neg1.of.Gt_0 h_d]
    simp


-- created on 2025-03-30
