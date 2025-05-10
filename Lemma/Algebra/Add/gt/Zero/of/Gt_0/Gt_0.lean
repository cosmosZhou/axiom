import Lemma.Algebra.EqAdd_0
import Lemma.Algebra.GtAddS.of.Gt.Gt
open Algebra


@[main]
private lemma main
  [AddZeroClass α]
  [Preorder α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]
  {a b : α}
-- given
  (h₀ : a > 0)
  (h₁ : b > 0) :
-- imply
  a + b > 0 := by
-- proof
  have h := GtAddS.of.Gt.Gt h₀ h₁
  simp only [EqAdd_0] at h
  exact h


-- created on 2024-11-25
-- updated on 2025-01-17
