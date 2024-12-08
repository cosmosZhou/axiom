import Axiom.Basic


namespace Algebra.OrAnd.to

theorem AndOrS
-- given
  (h : p ∧ q ∨ r) :
-- imply
  (p ∨ r) ∧ (q ∨ r) := by
-- proof
  cases h with
  | inl hpq =>
    have hp : p := hpq.left
    have hq : q := hpq.right
    exact ⟨Or.inl hp, Or.inl hq⟩
  | inr hr =>
    exact ⟨Or.inr hr, Or.inr hr⟩


end Algebra.OrAnd.to

-- created on 2024-07-01
