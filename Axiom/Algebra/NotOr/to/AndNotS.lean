import Axiom.Algebra.NotAnd.equ.OrNotS

namespace Algebra.NotOr.to

theorem AndNotS
-- given
  (h : ¬(p ∨ q)) :
-- imply
  ¬p ∧ ¬q := by
-- proof
  by_contra h_And
  rw [NotAnd.equ.OrNotS] at h_And
  simp at h_And
  contradiction


end Algebra.NotOr.to

-- created on 2024-07-01
