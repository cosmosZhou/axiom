import Axiom.Basic

namespace Algebra.Lt.to

theorem Le_Sub_1
  {x y : ℤ}
-- given
  (h : x < y) :
-- imply
  x ≤ y - 1 := by
-- proof
  linarith

end Algebra.Lt.to

-- created on 2024-07-01
