import Axiom.Basic


@[main]
private lemma nat
  [LinearOrderedRing R]
  [FloorRing R]
  {x : R}
  {d : ℕ} :
-- imply
  ⌊x + d⌋ = ⌊x⌋ + d := by
-- proof
  have := Int.floor_add_int x d
  norm_cast at this


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


-- created on 2025-03-04
-- updated on 2025-04-04
