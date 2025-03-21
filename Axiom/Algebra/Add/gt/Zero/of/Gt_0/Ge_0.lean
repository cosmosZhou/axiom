import Axiom.Algebra.EqAdd_0
import Axiom.Algebra.GtAddS.of.Gt.Ge
open Algebra


@[main]
private lemma main
  [AddZeroClass α]
  [Preorder α]
  [AddLeftStrictMono α] [AddLeftMono α]
  [AddRightStrictMono α] [AddRightMono α]
  {a b : α}
-- given
  (h₀ : a > 0)
  (h₁ : b ≥ 0) :
-- imply
  a + b > 0 := by
-- proof
  have h := GtAddS.of.Gt.Ge h₀ h₁
  simp only [EqAdd_0] at h
  exact h


-- created on 2025-01-17
