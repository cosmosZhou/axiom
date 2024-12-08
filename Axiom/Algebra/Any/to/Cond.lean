import Axiom.Basic


namespace Algebra.Any.to

theorem Cond
-- given
  (h : ∃ _ : α, r) :
-- imply
  r := by
-- proof
  let ⟨_, hr⟩ := h
  exact hr


end Algebra.Any.to

-- created on 2024-07-01
