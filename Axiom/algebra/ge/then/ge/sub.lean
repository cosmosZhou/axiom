import Mathlib.Tactic
import Axiom.algebra.ge.then.le.reverse
import Axiom.algebra.le.then.le.sub

namespace algebra.ge.then.ge

theorem sub
  {α : Type*} [OrderedAddCommGroup α]
  {x y : α}
-- given
  (h : x ≥ y)
  (z : α) :
-- imply
  x - z ≥ y - z:= by
-- proof
  have h' : y ≤ x := by
    apply algebra.ge.then.le.reverse h

  apply algebra.le.then.le.sub h' z


end algebra.ge.then.ge
open algebra.ge.then.ge
