import Axiom.Basic

namespace Algebra.Gt.to.Lt

theorem reverse
  {α : Type*} [LT α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  y < x := by
-- proof
  simp [h]


end Algebra.Gt.to.Lt

-- created on 2024-07-01
