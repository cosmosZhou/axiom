import Lemma.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {a : α}
-- given
  (h₀ : z - 1 < a)
  (h₁ : a ≤ z) :
-- imply
  ⌈a⌉ = z :=
-- proof
  Int.ceil_eq_iff.mpr ⟨h₀, h₁⟩


-- created on 2025-03-30
