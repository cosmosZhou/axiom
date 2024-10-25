import Mathlib.Tactic
import Axiom.algebra.gt.then.ge.add.one
import Axiom.algebra.ge.then.ge.sub

namespace algebra.gt.then.sub_ge.st

theorem one
  {x y : ℤ}
-- given
  (h : x > y):
-- imply
  x - 1 ≥ y := by
-- proof
  have h' : x ≥ y + 1 := by
    apply algebra.gt.then.ge.add.one h

  have h' : x - 1 ≥ y + 1 - 1 := by
    apply algebra.ge.then.ge.sub h' 1

  have h' : x - 1 ≥ y + (1 - 1) := by
    rw [add_sub_assoc] at h'
    exact h'

  have h' : x - 1 ≥ y + 0 := by
    rw [sub_self] at h'
    exact h'

  have h' : x - 1 ≥ y := by
    rw [add_zero] at h'
    exact h'

  exact h'

end algebra.gt.then.sub_ge.st
open algebra.gt.then.sub_ge.st
