import Axiom.Algebra.And_Or.equ.OrAndS
import Axiom.Algebra.And_.And.Not.equ.False

namespace Algebra.OrNotS.to

theorem NotAnd
-- given
  (h : ¬p ∨ ¬q) :
-- imply
  ¬(p ∧ q) := by
-- proof
  intro hpq
  have h := And.intro hpq h
  rw [And_Or.equ.OrAndS] at h

  simp [
    And_.And.Not.equ.False true,
    And_.And.Not.equ.False false
  ] at h


end Algebra.OrNotS.to

-- created on 2024-07-01
