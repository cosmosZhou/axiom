import Axiom.Basic

namespace Algebra.Lt.Lt.to.Lt

theorem trans
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a < b)
  (h₁ : b < c) :
-- imply
  a < c :=
-- proof
  lt_trans h₀ h₁


end Algebra.Lt.Lt.to.Lt

-- created on 2024-11-25
