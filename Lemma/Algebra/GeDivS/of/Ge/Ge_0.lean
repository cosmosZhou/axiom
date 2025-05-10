import Lemma.Algebra.Mul_Inv.eq.Div
import Lemma.Algebra.Inv.ge.Zero.of.Ge_0
import Lemma.Algebra.GeMulS.of.Ge.Ge_0
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
  (h₁ : x ≥ 0) :
-- imply
  a / x ≥ b / x := by
-- proof
  have : x⁻¹ ≥ 0 := Inv.ge.Zero.of.Ge_0 h₁
  have := GeMulS.of.Ge.Ge_0 h₀ this
  rw [
    Mul_Inv.eq.Div,
    Mul_Inv.eq.Div
  ] at this
  exact this


-- created on 2025-01-14
-- updated on 2025-03-30
