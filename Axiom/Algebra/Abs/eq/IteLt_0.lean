import Axiom.Algebra.Abs.eq.IteGe_0
import Axiom.Logic.Ite.eq.IteNot
open Algebra Logic


@[main]
private lemma main
  [LinearOrderedRing α]
  {x : α} :
-- imply
  |x| = if x < 0 then
    -x
  else
    x := by
-- proof
  rw [Ite.eq.IteNot]
  rw [Abs.eq.IteGe_0]
  simp


-- created on 2025-04-17
