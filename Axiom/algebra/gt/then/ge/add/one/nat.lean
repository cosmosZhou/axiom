import Mathlib.Tactic
import Axiom.algebra.gt.then.lt.reverse
import Axiom.algebra.lt.then.add_le.st.one.nat
import Axiom.algebra.le.then.ge.reverse

namespace algebra.gt.then.ge.add.one

theorem nat
  {x y : ℕ}
-- given
  (h : x > y):
-- imply
  x ≥ y + 1 := by
-- proof
  have h' : y < x := by
    apply algebra.gt.then.lt.reverse h

  have h' : y + 1 ≤ x := by
    apply algebra.lt.then.add_le.st.one.nat h'

  apply algebra.le.then.ge.reverse h'


end algebra.gt.then.ge.add.one
open algebra.gt.then.ge.add.one
