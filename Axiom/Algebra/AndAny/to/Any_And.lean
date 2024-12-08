import Axiom.Basic


namespace Algebra.AndAny.to

theorem Any_And
  {r :Prop}
  {p : α → Prop}
-- given
  (h : (∃ x : α, p x) ∧ r) :
-- imply
  ∃ x : α, p x ∧ r := by
-- proof
  let ⟨⟨x, hLeft⟩, hRight⟩ := h
  exact ⟨x, hLeft, hRight⟩


end Algebra.AndAny.to

-- created on 2024-07-01
