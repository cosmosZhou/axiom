import Axiom.Algebra.GtMulS.of.Gt.Gt_0
import Axiom.Algebra.Mul_Inv.eq.Div
import Axiom.Algebra.Inv.gt.Zero.of.Gt_0
open Algebra


@[main]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
-- given
  (h1 : a > b)
  (h2 : x > 0) :
-- imply
  a / x > b / x := by
-- proof
  have h3 : x⁻¹ > 0 := Inv.gt.Zero.of.Gt_0 h2
  have h4 := GtMulS.of.Gt.Gt_0 h1 h3
  rw [
    Mul_Inv.eq.Div, Mul_Inv.eq.Div
  ] at h4
  exact h4


-- created on 2024-11-25
