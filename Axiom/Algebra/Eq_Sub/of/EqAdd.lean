import Axiom.Algebra.EqSubS.of.Eq
import Axiom.Algebra.EqSubAdd
open Algebra


@[main]
private lemma main
  [AddGroup α]
  {x y d : α}
-- given
  (h : d + x = y) :
-- imply
  d = y - x := by
-- proof
  have h := EqSubS.of.Eq h x
  rw [EqSubAdd] at h
  exact h


-- created on 2024-07-01
