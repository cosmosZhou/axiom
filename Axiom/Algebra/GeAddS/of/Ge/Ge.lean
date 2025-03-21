import Axiom.Algebra.GeAddS.of.Ge
import Axiom.Algebra.Ge.of.Ge.Ge.trans
open Algebra


@[main]
private lemma main
  [Add α]
  [Preorder α]
  [AddRightMono α]
  [AddLeftMono α]
  {a b x y : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : x ≥ y) :
-- imply
  a + x ≥ b + y := by
-- proof
  have h₂ := GeAddS.of.Ge h₀ x
  have h₃ := GeAddS.of.Ge h₁ b true
  apply Ge.of.Ge.Ge.trans h₂ h₃


-- created on 2024-11-25
