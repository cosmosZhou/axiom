import Axiom.Basic


namespace Algebra.Le.Le.to.Le

theorem trans
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : b ≤ c) :
-- imply
  a ≤ c :=
-- proof
  le_trans h₀ h₁


end Algebra.Le.Le.to.Le

-- created on 2024-11-25
