import Axiom.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : x < b) :
-- imply
  x ∈ Ico a b :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2025-03-02
