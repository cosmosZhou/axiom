import Axiom.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {a : α} 
  (h : ⌈a⌉ = z):
-- imply
  z - 1 < a ∧ a ≤ z :=
-- proof
  Int.ceil_eq_iff.mp h


-- created on 2025-03-30
