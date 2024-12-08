import Axiom.Basic

namespace Algebra.Lt.to.Le


theorem relax
  {α : Type*} [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x ≤ y :=
-- proof
  le_of_lt h


end Algebra.Lt.to.Le

-- created on 2024-07-01
