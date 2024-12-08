import Axiom.Basic

namespace Algebra.Gt.Ge.to.Gt

theorem trans
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a > b)
  (h₁ : b ≥ c) :
-- imply
  a > c :=
-- proof
  gt_of_gt_of_ge h₀ h₁


end Algebra.Gt.Ge.to.Gt

-- created on 2024-11-29
