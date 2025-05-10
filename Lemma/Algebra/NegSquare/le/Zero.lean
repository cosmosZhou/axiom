import Lemma.Algebra.Square.ge.Zero
import Lemma.Algebra.Neg.le.Zero.of.Ge_0
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {a : α} :
-- imply
  -a² ≤ 0 := by
-- proof
  have h := Square.ge.Zero (a := a)
  apply Neg.le.Zero.of.Ge_0 h


-- created on 2024-11-29
