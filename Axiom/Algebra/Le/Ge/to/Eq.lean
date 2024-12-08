import Axiom.Basic

namespace Algebra.Le.Ge.to

theorem Eq
  [PartialOrder α]
  {a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : a ≥ b) :
-- imply
  a = b :=
-- proof
  le_antisymm h₀ h₁



end Algebra.Le.Ge.to

-- created on 2024-11-29
