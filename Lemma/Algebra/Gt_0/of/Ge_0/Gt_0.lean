import Lemma.Algebra.EqAdd_0
import Lemma.Algebra.GtAddS.of.Ge.Gt
open Algebra


@[main]
private lemma main
  [AddZeroClass α]
  [Preorder α]
  [AddLeftStrictMono α] [AddLeftMono α]
  [AddRightStrictMono α] [AddRightMono α]
  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b > 0) :
-- imply
  a + b > 0 := by
-- proof
  have h₂ := GtAddS.of.Ge.Gt h₀ h₁
  simp only [EqAdd_0] at h₂
  assumption


-- created on 2025-03-23
