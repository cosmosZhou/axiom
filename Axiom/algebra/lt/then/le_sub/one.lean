import Mathlib.Tactic

namespace algebra.lt.then.le_sub

theorem one
  {x y : ℤ}
-- given
  (h : x < y):
-- imply
  x ≤ y - 1 := by
-- proof
  have _ : x + 1 ≤ y := by linarith
  linarith

end algebra.lt.then.le_sub
open algebra.lt.then.le_sub
