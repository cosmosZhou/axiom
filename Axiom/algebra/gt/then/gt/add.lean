import Mathlib.Tactic
import Axiom.algebra.lt.then.gt.reverse
import Axiom.algebra.lt.then.lt.add

namespace algebra.gt.then.gt

theorem add
  {α : Type*} [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x > y)
  (z : α) :
-- imply
  x + z > y + z:= by
-- proof
  have h' : y < x := by
    apply algebra.lt.then.gt.reverse h

  apply algebra.lt.then.lt.add h' z


end algebra.gt.then.gt
open algebra.gt.then.gt
