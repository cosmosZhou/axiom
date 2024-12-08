import Axiom.Algebra.Gt_0.Gt_0.to.Mul.gt.Zero
import Axiom.Algebra.Lt_0.to.Neg.gt.Zero
namespace Algebra.Lt_0.Lt_0.to.Mul.gt

theorem Zero
  [LinearOrderedRing α]
  {a b : α}
-- given
  (h₀ : a < 0)
  (h₁ : b < 0) :
-- imply
  a * b > 0 := by
-- proof
  have h₀ := Lt_0.to.Neg.gt.Zero h₀
  have h₁ := Lt_0.to.Neg.gt.Zero h₁
  have h := Gt_0.Gt_0.to.Mul.gt.Zero h₀ h₁
  simp at h
  exact h


end Algebra.Lt_0.Lt_0.to.Mul.gt

-- created on 2024-11-25
