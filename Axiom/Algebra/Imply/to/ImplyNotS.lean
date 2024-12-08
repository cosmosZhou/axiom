import Axiom.Basic


namespace Algebra.Imply.to

theorem ImplyNotS
-- given
  (h : p → q) :
-- imply
  ¬q → ¬p := by
-- proof
  intro hq
  intro hp
  have h' := h hp
  contradiction


end Algebra.Imply.to

-- created on 2024-07-01
