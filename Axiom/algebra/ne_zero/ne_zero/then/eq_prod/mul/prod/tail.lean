import Mathlib.Tactic
import Axiom.algebra.ne_zero.then.eq.cons.tail
import Axiom.algebra.prod.cons.to.mul.prod
set_option linter.dupNamespace false

namespace algebra.ne_zero.ne_zero.then.eq_prod.mul.prod

theorem tail
  {shape : List ℕ}
-- given
  (h1: shape.length ≠ 0)
  (h2: shape[0] ≠ 0):
-- imply
  shape.prod = shape[0] * shape.tail.prod := by
-- proof
  -- Use the product property
  have h_prod : (shape[0]::shape.tail).prod = shape[0] * shape.tail.prod := by
    simp [algebra.prod.cons.to.mul.prod]

  have h_tail : shape.tail = shape.drop 1 := by simp

  have h_cons : shape = shape[0]::shape.tail := by
    apply algebra.ne_zero.then.eq.cons.tail h1

  rw [h_cons.symm] at h_prod
  exact h_prod

end algebra.ne_zero.ne_zero.then.eq_prod.mul.prod
open algebra.ne_zero.ne_zero.then.eq_prod.mul.prod
