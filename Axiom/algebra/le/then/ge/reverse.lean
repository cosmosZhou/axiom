import Mathlib.Tactic

namespace algebra.le.then.ge

theorem reverse
  {α : Type*} [LE α]
  {x y : α}
-- given
  (h : x ≤ y):
-- imply
  y ≥ x := by
-- proof
  exact h


end algebra.le.then.ge
open algebra.le.then.ge
