import Axiom.Algebra.FloorAdd.eq.AddFloor
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌊x⌋ + d = ⌊x + d⌋ := by
-- proof
  simp [FloorAdd.eq.AddFloor]


-- created on 2025-03-04
