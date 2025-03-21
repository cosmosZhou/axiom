import Axiom.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {a : α} :
-- imply
  ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a ≤ ↑z :=
-- proof
  Int.ceil_eq_iff


-- created on 2025-03-20
