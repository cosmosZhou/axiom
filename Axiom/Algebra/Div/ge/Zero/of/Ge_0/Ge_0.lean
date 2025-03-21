import Axiom.Algebra.GeDivS.of.Ge.Ge_0
import Axiom.Algebra.Div0.eq.Zero
open Algebra


@[main]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
-- imply
  a / b ≥ 0 := by
-- proof
  have h := GeDivS.of.Ge.Ge_0 h₀ h₁
  simp only [Div0.eq.Zero] at h
  exact h


-- created on 2025-01-14
