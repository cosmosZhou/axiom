import Lemma.Basic


@[main]
private lemma main
  [LinearOrderedRing α]
  {x y : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y ≥ 0)
  (h₂ : x ≤ 0 ∨ y ≤ 0) :
-- imply
  (x ≤ 0 ∨ y ≤ 0) ∧ (x ≥ 0 ∨ y ≥ 0) ∧ (x ≥ 0 ∧ y ≥ 0 ∨ x < 0 ∧ y < 0) := by
-- proof
  -- Use the given assumptions and logical implications to prove each conjunct.
  refine' ⟨h₂, Or.inl h₀, _⟩
  -- Since x and y are both non-negative, the disjunction simplifies to the first part.
  simp_all


-- created on 2025-04-18
-- updated on 2025-04-19
