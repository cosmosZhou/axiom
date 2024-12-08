import Axiom.Basic

namespace Algebra.Lt.to.Gt

theorem reverse
  {α : Type*} [LT α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  y > x := by
-- proof
  simp [h]


end Algebra.Lt.to.Gt

-- created on 2024-07-01
