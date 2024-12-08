import Axiom.Algebra.NotAll.to.Any_Not


namespace Algebra.NotAll_Not.to

theorem Any
  {p : α → Prop}
-- given
  (h : ¬∀ x : α, ¬p x) :
-- imply
  ∃ x : α, p x := by
-- proof
  have h := NotAll.to.Any_Not h
  simp at h
  exact h


end Algebra.NotAll_Not.to

-- created on 2024-07-01
