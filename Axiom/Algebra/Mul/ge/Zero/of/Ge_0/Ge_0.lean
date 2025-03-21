import Axiom.Algebra.GeMulS.of.Ge_0.Ge
import Axiom.Algebra.Mul_0.eq.Zero
open Algebra


@[main]
private lemma main
  [MulZeroClass α] [Preorder α] [PosMulMono α]
  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
-- imply
  a * b ≥ 0 := by
-- proof
  have h := GeMulS.of.Ge_0.Ge h₀ h₁
  simp only [Mul_0.eq.Zero] at h
  exact h


-- created on 2025-01-14
