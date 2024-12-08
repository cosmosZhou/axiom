import Axiom.Basic

namespace Algebra.Ge.to.Le

theorem reverse
  [LE α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  y ≤ x := by
-- proof
  exact h


end Algebra.Ge.to.Le

-- created on 2024-07-01
