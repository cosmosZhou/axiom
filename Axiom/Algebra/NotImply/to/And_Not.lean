import Axiom.Basic


namespace Algebra.NotImply.to

theorem And_Not
-- given
  (h : ¬(p → q)) :
-- imply
  p ∧ ¬q := by
-- proof
  simp at h
  exact h


end Algebra.NotImply.to

-- created on 2024-07-01
