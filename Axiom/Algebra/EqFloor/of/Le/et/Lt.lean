import Axiom.Algebra.EqFloor.is.Le.et.Lt
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {a : α}
-- given
  (h₀ : z ≤ a)
  (h₁ : a < z + 1) :
-- imply
  ⌊a⌋ = z :=
-- proof
  EqFloor.is.Le.et.Lt.mpr ⟨h₀, h₁⟩


-- created on 2025-03-30
