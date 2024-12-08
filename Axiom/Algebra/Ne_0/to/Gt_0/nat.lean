import Axiom.Basic

namespace Algebra.Ne_0.to.Gt_0

theorem nat
  {a : ℕ}
-- given
  (h : a ≠ 0) :
-- imply
  a > 0 := by
-- proof
  exact Nat.pos_of_ne_zero h


end Algebra.Ne_0.to.Gt_0

-- created on 2024-07-01
