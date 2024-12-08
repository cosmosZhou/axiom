import Axiom.Algebra.And_.And.Not.equ.False
import Axiom.Algebra.Iff_Not.to.Iff_Not
import Axiom.Algebra.Cond.to.Imply

namespace Algebra.AndAndNot.equ

@[simp]
theorem False :
-- imply
  (¬p ∧ q) ∧ p ↔ False := by
-- proof
  let p' := ¬p
  have h := Iff_Not.to.Iff_Not (show p' ↔ ¬p by rfl)

  rw [h]
  simp

  apply Cond.to.Imply




end Algebra.AndAndNot.equ

-- created on 2024-07-01
