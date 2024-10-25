import Mathlib.Tactic

namespace algebra.lt.then.lt

theorem sub
  {α : Type*} [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x < y)
  (z : α) :
-- imply
  x - z < y - z:= by
-- proof
  rw [sub_eq_add_neg x z, sub_eq_add_neg y z]
  apply add_lt_add_right h (-z)


end algebra.lt.then.lt
open algebra.lt.then.lt
