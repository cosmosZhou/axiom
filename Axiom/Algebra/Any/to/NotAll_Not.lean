import Axiom.Basic


namespace Algebra.Any.to

theorem NotAll_Not
  {p : α → Prop}
-- given
  (h : ∃ x : α, p x) :
-- imply
  ¬∀ x : α, ¬p x := by
-- proof
  intro h_All
  let ⟨x, h⟩ := h
  have h := h_All x
  contradiction


end Algebra.Any.to

-- created on 2024-07-01
