import Mathlib.Tactic

namespace algebra.le.then.le

theorem sub
  {α : Type*} [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x ≤ y)
  (z : α) :
-- imply
  x - z ≤ y - z := by
-- proof
  rw [sub_eq_add_neg x z, sub_eq_add_neg y z]
  apply add_le_add_right h (-z)


end algebra.le.then.le
open algebra.le.then.le
