import Axiom.Algebra.Lt.to.Ne

namespace Algebra.Gt.to

theorem Ne
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≠ y :=
  (Lt.to.Ne h).symm

end Algebra.Gt.to

-- created on 2024-07-01
