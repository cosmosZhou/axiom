import Axiom.Basic


namespace Algebra.And_Or.to

theorem OrAndS
  (h : p ∧ (q ∨ r)) :
-- imply
   p ∧ q ∨ p ∧ r := by
-- proof
  cases h with
  | intro hp hqr =>
    cases hqr with
    | inl hq => exact Or.inl ⟨hp, hq⟩
    | inr hr => exact Or.inr ⟨hp, hr⟩


end Algebra.And_Or.to

-- created on 2024-07-01
