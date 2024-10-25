import Mathlib.Tactic
import Axiom.algebra.gt.then.lt.reverse
import Axiom.algebra.lt.then.le.relax
import Axiom.algebra.le.then.ge.reverse


namespace algebra.gt.then.ge


theorem relax
  {α : Type*} [Preorder α]
  {x y : α}
-- given
  (h : x > y):
-- imply
  x ≥ y := by
-- proof
  have h := algebra.gt.then.lt.reverse h
  have h := algebra.lt.then.le.relax h
  apply algebra.le.then.ge.reverse h


end algebra.gt.then.ge
open algebra.gt.then.ge
