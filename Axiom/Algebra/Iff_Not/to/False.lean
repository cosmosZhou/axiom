import Axiom.Basic


namespace Algebra.Iff_Not.to

theorem False
  (h : p ↔ ¬p) :
-- imply
  False := by
-- proof
  simp [Iff] at h


end Algebra.Iff_Not.to

-- created on 2024-07-01
