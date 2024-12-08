import Axiom.Basic


namespace Algebra.Ge.Ge.to.Ge

theorem trans
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : b ≥ c) :
-- imply
  a ≥ c :=
-- proof
  ge_trans h₀ h₁


end Algebra.Ge.Ge.to.Ge

-- created on 2024-11-25
