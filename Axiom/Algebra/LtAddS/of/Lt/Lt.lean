import Axiom.Algebra.LtAddS.of.Lt
import Axiom.Algebra.Lt.of.Lt.Lt
open Algebra


@[main]
private lemma main
  [Add α]
  [Preorder α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]
  {a b x y : α}
-- given
  (h₀ : a < b)
  (h₁ : x < y) :
-- imply
  a + x < b + y := by
-- proof
  have h₂ := Algebra.LtAddS.of.Lt h₀ x
  have h₃ := Algebra.LtAddS.of.Lt h₁ b true
  apply Lt.of.Lt.Lt h₂ h₃


-- created on 2024-11-25
