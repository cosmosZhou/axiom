import Axiom.Algebra.Add.comm
import Axiom.Algebra.FloorAdd.eq.AddFloor
open Algebra


@[main]
private lemma nat
  [LinearOrderedRing α]
  [FloorRing α]
  {x : α}
  {d : ℕ} :
-- imply
  ⌊d + x⌋ = d + ⌊x⌋ := by
-- proof
  rw [Add.comm]
  rw [FloorAdd.eq.AddFloor.nat]
  rw [Add.comm]


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


-- created on 2025-03-15
-- updated on 2025-04-04
