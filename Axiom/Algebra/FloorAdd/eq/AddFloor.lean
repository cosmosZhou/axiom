import Axiom.Basic


@[main]
private lemma main
  [LinearOrderedRing R]
  [FloorRing R]
  {x : R}
  {d : ℤ} :
-- imply
  ⌊x + d⌋ = ⌊x⌋ + d := by
-- proof
  apply Int.floor_add_int


@[main]
private lemma nat
  [LinearOrderedRing R]
  [FloorRing R]
  {x : R}
  {d : ℕ} :
-- imply
  ⌊x + d⌋ = ⌊x⌋ + d := by
-- proof
  have := main (x := x) (d := d)
  norm_cast at this


@[main]
private lemma one
  [LinearOrderedRing R]
  [FloorRing R]
  {x : R} :
-- imply
  ⌊x + 1⌋ = ⌊x⌋ + 1 := by
-- proof
  have := nat (x := x) (d := 1)
  norm_cast at this


-- created on 2025-03-04
