import Mathlib.Tactic

namespace algebra.le.then.le

theorem add
  {α : Type*} [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x ≤ y)
  (z : α) :
-- imply
  x + z ≤ y + z:= by
-- proof
  apply add_le_add_right h z


end algebra.le.then.le
open algebra.le.then.le
