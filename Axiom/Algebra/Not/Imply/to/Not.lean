import Axiom.Basic


namespace Algebra.Not.Imply.to

theorem Not
-- given
  (h₀ : ¬q)
  (h₁ : p → q) :
-- imply
  ¬p :=
-- proof
  fun p ↦ h₀ (h₁ p)


end Algebra.Not.Imply.to

-- created on 2024-07-01
