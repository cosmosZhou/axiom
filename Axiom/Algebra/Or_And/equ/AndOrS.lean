import Axiom.Algebra.OrAnd.equ.AndOrS


namespace Algebra.Or_And.equ

theorem AndOrS :
-- imply
  r ∨ p ∧ q ↔ (r ∨ p) ∧ (r ∨ q) := by
-- proof
  rw [
    Or.comm,
    Or.comm (a := r),
    Or.comm (a := r)
  ]
  apply OrAnd.equ.AndOrS


end Algebra.Or_And.equ

-- created on 2024-07-01
