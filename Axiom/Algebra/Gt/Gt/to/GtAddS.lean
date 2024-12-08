import Axiom.Algebra.Gt.to.GtAddS
import Axiom.Algebra.Gt.Gt.to.Gt.trans


namespace Algebra.Gt.Gt.to

theorem GtAddS
  [Add α]
  [Preorder α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]
  {a b x y : α}
-- given
  (h₀ : a > b)
  (h₁ : x > y) :
-- imply
  a + x > b + y := by
-- proof
  have h₂ := Algebra.Gt.to.GtAddS h₀ x
  have h₃ := Algebra.Gt.to.GtAddS h₁ b true
  apply Gt.Gt.to.Gt.trans h₂ h₃


end Algebra.Gt.Gt.to

-- created on 2024-11-25
