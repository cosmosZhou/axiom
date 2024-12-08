import Axiom.Algebra.Lt.to.Le.relax

namespace Algebra.Gt.to.Ge


theorem relax
  {α : Type*} [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≥ y := by
-- proof
  exact Lt.to.Le.relax h


end Algebra.Gt.to.Ge

-- created on 2024-07-01
