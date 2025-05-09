import Axiom.Algebra.Square.ge.Zero
import Axiom.Algebra.Eq.of.Le.Ge
import Axiom.Algebra.Eq_0.of.Square.eq.Zero
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x : α}
-- given
  (h : x² ≤ 0) :
-- imply
  x = 0 := by
-- proof
  have := Square.ge.Zero (a := x)
  have := Eq.of.Le.Ge h this
  apply Eq_0.of.Square.eq.Zero this


-- created on 2025-04-06
