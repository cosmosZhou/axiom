import Axiom.Basic


namespace Algebra.OrAndS.to

theorem And_Or
  (h : p ∧ q ∨ p ∧ r) :
-- imply
  p ∧ (q ∨ r) := by
-- proof
  cases h with
  | inl hpq =>
    cases hpq with
    | intro hp hq => exact ⟨hp, Or.inl hq⟩
  | inr hpr =>
    cases hpr with
    | intro hp hr => exact ⟨hp, Or.inr hr⟩


end Algebra.OrAndS.to

-- created on 2024-07-01
