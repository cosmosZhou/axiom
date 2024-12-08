import Axiom.Algebra.Ge.Ge.to.GeAddS
import Axiom.Algebra.Add_0.simp


namespace Algebra.Ge_0.Ge_0.to.Add.ge

theorem Zero
  [AddZeroClass α]
  [Preorder α]
  [AddRightMono α]
  [AddLeftMono α]

  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
-- imply
  a + b ≥ 0 := by
-- proof
  have h := Ge.Ge.to.GeAddS h₀ h₁
  simp only [Add_0.simp] at h
  exact h


end Algebra.Ge_0.Ge_0.to.Add.ge

-- created on 2024-11-25
