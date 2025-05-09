import Axiom.Algebra.FloorAdd.eq.AddFloor
open Algebra


@[main]
private lemma main
  [LinearOrderedRing R]
  [FloorRing R]
  {x : R} :
-- imply
  ⌊x + 1⌋ =   ⌊x⌋ + 1 := by
-- proof
  have := FloorAdd.eq.AddFloor (x := x) (d := 1)
  norm_cast at this


-- created on 2025-03-25
