import Axiom.Basic


namespace Algebra.AndOrS.to

theorem OrAnd
-- given
  (h : (p ∨ r) ∧ (q ∨ r)) :
-- imply
  p ∧ q ∨ r := by
-- proof
  have hpr : p ∨ r := h.left
  have hqr : q ∨ r := h.right
  cases hpr with
  | inl hp =>
    cases hqr with
    | inl hq =>
      exact Or.inl ⟨hp, hq⟩
    | inr hr =>
      exact Or.inr hr
  | inr hr =>
    exact Or.inr hr


end Algebra.AndOrS.to

-- created on 2024-07-01
