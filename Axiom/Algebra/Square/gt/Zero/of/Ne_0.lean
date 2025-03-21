import Axiom.Algebra.Square.ge.Zero
import Axiom.Algebra.Square.ne.Zero.of.Ne_0
import Axiom.Algebra.Gt.of.Ne.Ge
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a² > 0 :=
-- proof
  Gt.of.Ne.Ge
    (Square.ne.Zero.of.Ne_0 h)
    (Square.ge.Zero (a := a))


-- created on 2024-11-29
