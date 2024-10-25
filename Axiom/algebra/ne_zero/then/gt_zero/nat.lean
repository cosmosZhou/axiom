import Mathlib.Tactic

namespace algebra.ne_zero.then.gt_zero

theorem nat
  {a : ℕ}
-- given
  (h : a ≠ 0):
-- imply
  a > 0 := by
-- proof
    exact Nat.pos_of_ne_zero h


end algebra.ne_zero.then.gt_zero
open algebra.ne_zero.then.gt_zero
