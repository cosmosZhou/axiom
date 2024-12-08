import Axiom.Basic

namespace Algebra.Ne_0.to.EqDivMul

@[simp]
theorem cancel
  [Field α]
  {a b : α}
-- given
  (h : a ≠ 0) :
-- imply
  a * b / a = b := by
-- proof
  simp [h]


end Algebra.Ne_0.to.EqDivMul

-- created on 2024-07-01
