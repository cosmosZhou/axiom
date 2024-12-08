import Axiom.Algebra.AndAndNot.equ.False
namespace Algebra.AndAnd_Not.equ

@[simp]
theorem False :
-- imply
  (q ∧ ¬p) ∧ p ↔ False := by
-- proof
  rw [And.comm (a := q)]
  apply AndAndNot.equ.False


end Algebra.AndAnd_Not.equ

-- created on 2024-07-01
