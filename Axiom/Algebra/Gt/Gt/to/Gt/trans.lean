import Axiom.Basic


namespace Algebra.Gt.Gt.to.Gt

theorem trans
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a > b)
  (h₁ : b > c) :
-- imply
  a > c :=
-- proof
  gt_trans h₀ h₁


end Algebra.Gt.Gt.to.Gt

-- created on 2024-11-25
