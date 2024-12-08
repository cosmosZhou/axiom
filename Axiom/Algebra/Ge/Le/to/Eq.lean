import Axiom.Algebra.Le.Ge.to.Eq

namespace Algebra.Ge.Le.to

theorem Eq
  [PartialOrder α]
  {a b : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : a ≤ b) :
-- imply
  a = b :=
-- proof
  Le.Ge.to.Eq h₁ h₀


end Algebra.Ge.Le.to

-- created on 2024-11-29
