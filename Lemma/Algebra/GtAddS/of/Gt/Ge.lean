import Lemma.Algebra.GtAddS.of.Gt
import Lemma.Algebra.GeAddS.of.Ge
import Lemma.Algebra.Gt.of.Gt.Ge
open Algebra


@[main]
private lemma main
  [Add α]
  [Preorder α]
  [AddLeftStrictMono α] [AddLeftMono α]
  [AddRightStrictMono α] [AddRightMono α]
  {a b x y : α}
-- given
  (h₀ : a > b)
  (h₁ : x ≥ y) :
-- imply
  a + x > b + y := by
-- proof
  have h₂ := GtAddS.of.Gt h₀ x
  have h₃ := GeAddS.of.Ge.left h₁ b
  apply Gt.of.Gt.Ge h₂ h₃


-- created on 2025-01-17
-- updated on 2025-04-30
