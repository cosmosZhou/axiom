import Axiom.Basic

namespace Algebra.Lt.to.Le_Sub_1

theorem nat
  {x y : ℕ}
-- given
  (h : x < y) :
-- imply
  x ≤ y - 1 := by
-- proof
  exact Nat.le_pred_of_lt h


end Algebra.Lt.to.Le_Sub_1

-- created on 2024-07-01
