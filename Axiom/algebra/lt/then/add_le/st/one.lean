import Mathlib.Tactic
import Axiom.algebra.lt.then.le_sub.one
import Axiom.algebra.le.then.le.add

namespace algebra.lt.then.add_le.st

theorem one
  {x y : ℤ}
-- given
  (h : x < y):
-- imply
  x + 1 ≤ y := by
-- proof
  have h' : x ≤ y - 1 := by
    apply algebra.lt.then.le_sub.one h

  have h' : x + 1 ≤ y - 1 + 1 := by
    apply algebra.le.then.le.add h' 1

  have h' : x + 1 ≤ y := by
    rw [sub_add_cancel] at h'
    exact h'

  exact h'

end algebra.lt.then.add_le.st
open algebra.lt.then.add_le.st
