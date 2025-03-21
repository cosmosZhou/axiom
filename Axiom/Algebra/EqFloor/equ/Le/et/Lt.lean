import Axiom.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {a : α} :
-- imply
  ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < ↑z + 1 :=
-- proof
  Int.floor_eq_iff


-- created on 2025-03-20
