import Axiom.Algebra.Gt_0.Gt.to.GtMulS
import Axiom.Algebra.Mul_0.eq.Zero

namespace Algebra.Gt_0.Gt_0.to.Mul.gt

theorem Zero
  [MulZeroClass α] [Preorder α] [PosMulStrictMono α]
  {a b : α}
-- given
  (h₀ : a > 0)
  (h₁ : b > 0) :
-- imply
  a * b > 0 := by
-- proof
  -- apply mul_pos h₀ h₁
  have h := Gt_0.Gt.to.GtMulS h₀ h₁
  simp only [Mul_0.eq.Zero] at h
  exact h


end Algebra.Gt_0.Gt_0.to.Mul.gt

-- created on 2024-11-25
