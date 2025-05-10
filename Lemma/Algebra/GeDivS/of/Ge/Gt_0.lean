import Lemma.Algebra.GeMulS.of.Ge.Gt_0
import Lemma.Algebra.Mul_Inv.eq.Div
import Lemma.Algebra.Inv.gt.Zero.of.Gt_0
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
  (h₀ : a ≥ b)
  (h₁ : x > 0) :
-- imply
  a / x ≥ b / x := by
-- proof
  have : x⁻¹ > 0 := Inv.gt.Zero.of.Gt_0 h₁
  have := GeMulS.of.Ge.Gt_0 h₀ this
  rw [
    Mul_Inv.eq.Div,
    Mul_Inv.eq.Div
  ] at this
  assumption


-- created on 2024-11-25
-- updated on 2025-03-21
