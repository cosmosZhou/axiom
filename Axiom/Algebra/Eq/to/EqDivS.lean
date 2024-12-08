import Axiom.Basic

namespace Algebra.Eq.to

theorem EqDivS
  [Div α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  x / d = y / d := by
-- proof
  rw [h]

end Algebra.Eq.to

-- created on 2024-07-01
