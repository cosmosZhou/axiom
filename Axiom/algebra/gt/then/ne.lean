import Mathlib.Tactic
import Axiom.algebra.lt.then.ne
import Axiom.algebra.gt.then.lt.reverse
import Axiom.algebra.ne.then.ne.reverse

namespace algebra.gt.then

theorem ne
  {α : Type*} [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≠ y := by
-- proof
  have h' : y < x := by
    apply algebra.gt.then.lt.reverse h

  have h' : y ≠ x := by
    apply algebra.lt.then.ne h'

  apply algebra.ne.then.ne.reverse h'

end algebra.gt.then
open algebra.gt.then
