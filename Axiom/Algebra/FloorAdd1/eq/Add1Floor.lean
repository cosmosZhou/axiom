import Axiom.Algebra.FloorAdd.eq.Add_Floor
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌊1 + x⌋ = 1 +   ⌊x⌋ := by
-- proof
  have := FloorAdd.eq.Add_Floor (x := x) (d := 1)
  norm_cast at this


-- created on 2025-03-25
