import sympy.core.power
import Lemma.Algebra.Square.gt.Zero.of.Ne_0
import Lemma.Algebra.Ne.of.Gt
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {a : α}
-- given
  (h : a > 0) :
-- imply
  a² > 0 := by
-- proof
  have := Ne.of.Gt h
  apply Square.gt.Zero.of.Ne_0 this


-- created on 2025-04-06
