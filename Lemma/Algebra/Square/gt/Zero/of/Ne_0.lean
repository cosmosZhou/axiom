import Lemma.Algebra.Square.ge.Zero
import Lemma.Algebra.Square.ne.Zero.of.Ne_0
import Lemma.Algebra.Gt.of.Ge.Ne
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
  Gt.of.Ge.Ne
    (Square.ge.Zero (a := a))
    (Square.ne.Zero.of.Ne_0 h)


-- created on 2024-11-29
-- updated on 2025-03-30
