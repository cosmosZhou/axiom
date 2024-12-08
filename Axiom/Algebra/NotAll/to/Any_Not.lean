import Axiom.Basic


namespace Algebra.NotAll.to

theorem Any_Not
  {p : α → Prop}
-- given
  (h : ¬∀ x : α, p x) :
-- imply
  ∃ x : α, ¬p x := by
-- proof
  push_neg at h
  exact h


end Algebra.NotAll.to

-- created on 2024-07-01
