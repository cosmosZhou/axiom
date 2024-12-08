import Axiom.Basic

namespace Algebra.Lt.to

theorem Ne
  {α : Type*} [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x ≠ y :=
-- proof
  ne_of_lt h


end Algebra.Lt.to

-- created on 2024-07-01
