import Axiom.Basic

namespace Algebra.Eq.to.EqAddS

theorem left
  [Add α]
  {x y d : α}
-- given
  (h : x = y) :
-- imply
  d + x = d + y := by
-- proof
  rw [h]

end Algebra.Eq.to.EqAddS

-- created on 2024-07-01
