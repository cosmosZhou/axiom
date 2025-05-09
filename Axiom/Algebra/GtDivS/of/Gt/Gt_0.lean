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
  (h₀ : a > b)
  (h₁ : x > 0) :
-- imply
  a / x > b / x := by
-- proof
  have h₂ : x⁻¹ > 0 := Inv.gt.Zero.of.Gt_0 h₁
  have h₃ := GtMulS.of.Gt.Gt_0 h₀ h₂
  rw [
    Mul_Inv.eq.Div, Mul_Inv.eq.Div
  ] at h₃
  exact h₃


-- created on 2024-11-25
