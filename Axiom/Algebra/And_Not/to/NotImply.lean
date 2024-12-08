import Axiom.Basic


namespace Algebra.And_Not.to

theorem NotImply
-- given
  (h : p ∧ ¬q) :
-- imply
  ¬(p → q) := by
-- proof
  simp
  exact h


end Algebra.And_Not.to

-- created on 2024-07-01
