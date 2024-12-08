import Axiom.Algebra.Ge.to.GeAddS
import Axiom.Algebra.Ge.Ge.to.Ge.trans


namespace Algebra.Ge.Ge.to

theorem GeAddS
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
  have h₂ := Algebra.Ge.to.GeAddS h₀ x
  have h₃ := Algebra.Ge.to.GeAddS h₁ b true
  apply Ge.Ge.to.Ge.trans h₂ h₃


end Algebra.Ge.Ge.to

-- created on 2024-11-25
