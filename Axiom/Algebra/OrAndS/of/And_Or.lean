import Axiom.Basic


@[main]
private lemma main
-- given
  (h : p ∧ (q ∨ r)) :
-- imply
   p ∧ q ∨ p ∧ r := by
-- proof
  cases h with
  | intro hp hqr =>
    cases hqr with
    | inl hq => exact Or.inl ⟨hp, hq⟩
    | inr hr => exact Or.inr ⟨hp, hr⟩


-- created on 2024-07-01
