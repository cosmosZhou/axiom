import Mathlib.Tactic
import Axiom.algebra.gt.then.lt.reverse
import Axiom.algebra.lt.then.le_sub.one.nat

namespace algebra.gt.then.sub_ge.st.one

theorem nat
  {x y : ℕ}
-- given
  (h : x > y):
-- imply
  x - 1 ≥ y := by
-- proof
  have h1 : y < x := by
    apply algebra.gt.then.lt.reverse h
  apply algebra.lt.then.le_sub.one.nat h1


end algebra.gt.then.sub_ge.st.one
open algebra.gt.then.sub_ge.st.one
