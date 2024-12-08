import Axiom.Algebra.Le.to.LeAddS
import Axiom.Algebra.Le.Le.to.Le.trans


namespace Algebra.Le.Le.to

theorem LeAddS
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
  have h₂ := Algebra.Le.to.LeAddS h₀ x
  have h₃ := Algebra.Le.to.LeAddS h₁ b true
  apply Le.Le.to.Le.trans h₂ h₃


end Algebra.Le.Le.to

-- created on 2024-11-25
