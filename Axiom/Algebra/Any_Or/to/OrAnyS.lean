import Axiom.Basic


namespace Algebra.Any_Or.to

theorem OrAnyS
  {p q : α → Prop}
-- given
  (h : ∃ x : α, p x ∨ q x) :
-- imply
  (∃ x : α, p x) ∨ (∃ x : α, q x) := by
-- proof
  let ⟨x, hpq⟩ := h
  cases hpq with
  | inl hp =>
    left
    exact ⟨x, hp⟩
  | inr hq =>
    right
    exact ⟨x, hq⟩


end Algebra.Any_Or.to

-- created on 2024-07-01
