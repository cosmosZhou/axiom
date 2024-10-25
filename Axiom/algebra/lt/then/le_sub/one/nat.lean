import Mathlib.Tactic

namespace algebra.lt.then.le_sub.one

theorem nat
  {x y : ℕ}
-- given
  (h : x < y):
-- imply
  x ≤ y - 1 := by
-- proof
  exact Nat.le_pred_of_lt h


end algebra.lt.then.le_sub.one
open algebra.lt.then.le_sub.one
