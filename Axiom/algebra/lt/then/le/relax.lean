import Mathlib.Tactic

namespace algebra.lt.then.le


theorem relax
  {α : Type*} [Preorder α]
  {x y : α}
-- given
  (h : x < y):
-- imply
  x ≤ y := by
-- proof
  exact le_of_lt h


end algebra.lt.then.le
open algebra.lt.then.le
