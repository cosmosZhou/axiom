import Axiom.Algebra.Le.of.Lt_Add_1
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : y + 1 > x) :
-- imply
  y ≥ x := by
-- proof
  apply Le.of.Lt_Add_1 h


-- created on 2025-03-29
