import Lemma.Set.Mem_IcoFloor
open Set


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌊x⌋ ≤ x := by
-- proof
  have := Mem_IcoFloor (x := x)
  exact this.left


-- created on 2025-05-04
