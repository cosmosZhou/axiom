import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ≤ b)
  (h₁ : x ≥ a) :
-- imply
  x ∈ Icc a b := by
-- proof
  constructor <;>
    assumption


-- created on 2025-03-30
