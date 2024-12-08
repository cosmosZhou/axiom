import Axiom.Basic


namespace Algebra.OrAnyS.to

theorem Any_Or
  {p q : α → Prop}
-- given
  (h : (∃ x : α, p x) ∨ (∃ x : α, q x)) :
-- imply
  ∃ x : α, p x ∨ q x := by
-- proof
  cases h with
  | inl h_p =>
    let ⟨x, hp⟩ := h_p
    exact ⟨x, Or.inl hp⟩
  | inr h_q =>
    let ⟨x, hq⟩ := h_q
    exact ⟨x, Or.inr hq⟩


end Algebra.OrAnyS.to

-- created on 2024-07-01
