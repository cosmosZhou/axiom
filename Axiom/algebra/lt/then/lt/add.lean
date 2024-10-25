import Mathlib.Tactic

namespace algebra.lt.then.lt

theorem add
  {α : Type*} [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x < y)
  (z : α) :
-- imply
  x + z < y + z:= by
-- proof
  apply add_lt_add_right h z


end algebra.lt.then.lt
open algebra.lt.then.lt
