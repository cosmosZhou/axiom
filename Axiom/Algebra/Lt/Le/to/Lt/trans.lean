import Axiom.Basic

namespace Algebra.Lt.Le.to.Lt

theorem trans
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a < b)
  (h₁ : b ≤ c) :
-- imply
  a < c :=
-- proof
  lt_of_lt_of_le h₀ h₁


end Algebra.Lt.Le.to.Lt

-- created on 2024-11-29
