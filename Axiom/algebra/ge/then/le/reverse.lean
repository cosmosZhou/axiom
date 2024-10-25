import Mathlib.Tactic

namespace algebra.ge.then.le

theorem reverse
  {α : Type*} [LE α]
  {x y : α}
-- given
  (h : x ≥ y):
-- imply
  y ≤ x := by
-- proof
  exact h


end algebra.ge.then.le
open algebra.ge.then.le
