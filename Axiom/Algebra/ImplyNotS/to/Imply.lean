import Axiom.Algebra.Imply.to.ImplyNotS

namespace Algebra.ImplyNotS.to

theorem Imply
-- given
  (h : ¬p → ¬q) :
-- imply
  q → p := by
-- proof
  have h := Imply.to.ImplyNotS h
  simp at h
  exact h


end Algebra.ImplyNotS.to

-- created on 2024-07-01
