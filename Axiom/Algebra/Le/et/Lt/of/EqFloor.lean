import Axiom.Algebra.EqFloor.is.Le.et.Lt
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {a : α}
-- given
  (h : ⌊a⌋ = z) :
-- imply
  ↑z ≤ a ∧ a < ↑z + 1 :=
-- proof
  EqFloor.is.Le.et.Lt.mp h


-- created on 2025-03-30
