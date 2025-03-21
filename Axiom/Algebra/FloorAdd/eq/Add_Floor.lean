import Axiom.Algebra.Add.comm
import Axiom.Algebra.FloorAdd.eq.AddFloor
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℤ} :
-- imply
  ⌊d + x⌋ = d + ⌊x⌋ := by
-- proof
  rw [Add.comm]
  rw [FloorAdd.eq.AddFloor]
  rw [Add.comm]


@[main]
private lemma nat
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℕ} :
-- imply
  ⌊d + x⌋ = d + ⌊x⌋ := by
-- proof
  have := main (x := x) (d := d)
  norm_cast at this


@[main]
private lemma one
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌊1 + x⌋ = 1 + ⌊x⌋ := by
-- proof
  have := nat (x := x) (d := 1)
  norm_cast at this


-- created on 2025-03-15
