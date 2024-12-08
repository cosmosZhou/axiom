import Axiom.Basic

namespace Algebra.Ne_0.to.Div.eq

@[simp]
theorem One
  [GroupWithZero α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a / a = 1 := by
-- proof
  simp [h]

end Algebra.Ne_0.to.Div.eq

-- created on 2024-07-01
