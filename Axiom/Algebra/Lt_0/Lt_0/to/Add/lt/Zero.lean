import Axiom.Algebra.Lt.Lt.to.LtAddS
import Axiom.Algebra.Add_0.simp


namespace Algebra.Lt_0.Lt_0.to.Add.lt

theorem Zero
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
  have h := Lt.Lt.to.LtAddS h₀ h₁
  simp only [Add_0.simp] at h
  exact h


end Algebra.Lt_0.Lt_0.to.Add.lt

-- created on 2024-11-25
