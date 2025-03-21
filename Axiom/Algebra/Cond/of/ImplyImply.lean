import Axiom.Algebra.And_Not.of.NotImply
import Axiom.Algebra.ImplyNotS.of.Imply
import Axiom.Algebra.False.of.AndNot
open Algebra


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : (p → q) → p) :
-- imply
  p := by
-- proof
  by_contra hq
  have h' := ImplyNotS.of.Imply h
  have h' := And_Not.of.NotImply (h' hq)
  apply False.of.AndNot (And.intro hq h'.left)


-- created on 2024-07-01
