import Mathlib.Tactic

namespace algebra.gt.then.lt

theorem reverse
  {α : Type*} [LT α]
  {x y : α}
-- given
  (h : x > y):
-- imply
  y < x := by
-- proof
  simp [h]


end algebra.gt.then.lt
open algebra.gt.then.lt
