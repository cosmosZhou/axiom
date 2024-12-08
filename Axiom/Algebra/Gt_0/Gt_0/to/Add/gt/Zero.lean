import Axiom.Algebra.Gt.Gt.to.GtAddS
import Axiom.Algebra.Add_0.simp

namespace Algebra.Gt_0.Gt_0.to.Add.gt

theorem Zero
  [AddZeroClass α]
  [Preorder α]
  [AddRightStrictMono α]
  [AddLeftStrictMono α]

  {a b : α}
-- given
  (h₀ : a > 0)
  (h₁ : b > 0) :
-- imply
  a + b > 0 := by
-- proof
  have h := Gt.Gt.to.GtAddS h₀ h₁
  simp only [Add_0.simp] at h
  exact h


end Algebra.Gt_0.Gt_0.to.Add.gt

-- created on 2024-11-25
