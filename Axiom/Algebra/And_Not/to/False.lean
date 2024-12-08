import Axiom.Algebra.AndNot.to.False

namespace Algebra.And_Not.to

theorem False
-- given
  (h : p ∧ ¬p) :
-- imply
  False := by
-- proof
  rw [And.comm] at h
  apply AndNot.to.False h


end Algebra.And_Not.to

-- created on 2024-07-01
