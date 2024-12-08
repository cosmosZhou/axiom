import Axiom.Basic

namespace Algebra.Le.to.Ge

theorem reverse
  {α : Type*} [LE α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  y ≥ x := by
-- proof
  exact h


end Algebra.Le.to.Ge

-- created on 2024-07-01
