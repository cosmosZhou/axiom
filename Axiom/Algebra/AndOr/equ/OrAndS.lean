import Axiom.Algebra.And_Or.equ.OrAndS

namespace Algebra.AndOr.equ

theorem OrAndS :
-- imply
  (q ∨ r) ∧ p ↔ q ∧ p ∨ r ∧ p := by
-- proof
  rw [And.comm]
  rw [And_Or.equ.OrAndS]
  rw [And.comm]
  rw [And.comm (b := r)]


end Algebra.AndOr.equ

-- created on 2024-07-01
