import Axiom.Algebra.LeAddS.of.Le
import Axiom.Algebra.Le.of.Le.Le
open Algebra


@[main]
private lemma main
  [Add α]
  [Preorder α]
  [AddRightMono α]
  [AddLeftMono α]
  {a b x y : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x ≤ y) :
-- imply
  a + x ≤ b + y := by
-- proof
  have h₂ := LeAddS.of.Le h₀ x
  have h₃ := LeAddS.of.Le h₁ b true
  apply Le.of.Le.Le h₂ h₃


-- created on 2024-11-25
