import Axiom.Algebra.Lt.to.LtAddS
import Axiom.Algebra.Lt.Lt.to.Lt.trans

namespace Algebra.Lt.Lt.to

theorem LtAddS
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
  have h₂ := Algebra.Lt.to.LtAddS h₀ x
  have h₃ := Algebra.Lt.to.LtAddS h₁ b true
  apply Lt.Lt.to.Lt.trans h₂ h₃


end Algebra.Lt.Lt.to

-- created on 2024-11-25
