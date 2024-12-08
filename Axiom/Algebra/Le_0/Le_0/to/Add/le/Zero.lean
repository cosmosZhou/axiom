import Axiom.Algebra.Le.Le.to.LeAddS
import Axiom.Algebra.Add_0.simp


namespace Algebra.Le_0.Le_0.to.Add.le

theorem Zero
  [AddZeroClass α]
  [Preorder α]
  [AddRightMono α]
  [AddLeftMono α]

  {a b : α}
-- given
  (h₀ : a ≤ 0)
  (h₁ : b ≤ 0) :
-- imply
  a + b ≤ 0 := by
-- proof
  have h := Le.Le.to.LeAddS h₀ h₁
  simp only [Add_0.simp] at h
  exact h


end Algebra.Le_0.Le_0.to.Add.le

-- created on 2024-11-25
