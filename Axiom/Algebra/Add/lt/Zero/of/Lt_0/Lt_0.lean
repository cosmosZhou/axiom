import Axiom.Algebra.EqAdd_0
import Axiom.Algebra.LtAddS.of.Lt.Lt
open Algebra


@[main]
private lemma main
  [AddZeroClass α]
  [Preorder α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]
  {a b : α}
-- given
  (h₀ : a < 0)
  (h₁ : b < 0) :
-- imply
  a + b < 0 := by
-- proof
  have h := LtAddS.of.Lt.Lt h₀ h₁
  simp only [EqAdd_0] at h
  exact h


-- created on 2024-11-25
-- updated on 2025-01-17
