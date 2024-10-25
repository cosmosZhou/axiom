import Mathlib.Tactic

namespace algebra.lt.then.gt

theorem reverse
  {α : Type*} [LT α]
  {x y : α}
-- given
  (h : x < y):
-- imply
  y > x := by
-- proof
  simp [h]


end algebra.lt.then.gt
open algebra.lt.then.gt
