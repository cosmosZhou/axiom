import Axiom.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {n : ℤ}
  {x : α}
-- given
  (h : x ≥ n) :
-- imply
  ⌊x⌋ ≥ n :=
-- proof
  Int.le_floor.mpr h


-- created on 2025-05-05
