import Mathlib.Tactic
import Axiom.algebra.ne_zero.ne_zero.then.eq_prod.mul.prod.tail
import Axiom.algebra.eq.then.eq.div

set_option linter.dupNamespace false

namespace algebra.ne_zero.ne_zero.then.eq.prod

theorem tail
  {shape : List ℕ}
-- given
  (h1: shape.length ≠ 0)
  (h2: shape[0] ≠ 0) :
-- imply
  shape.tail.prod = shape.prod / shape[0] := by
-- proof
  -- Use the product property
  have h_prod := algebra.ne_zero.ne_zero.then.eq_prod.mul.prod.tail h1 h2

  -- divide both sides by shape[0]
  have h_div : shape.prod / shape[0] = shape[0] * shape.tail.prod / shape[0] := by
    apply algebra.eq.then.eq.div h_prod shape[0]

  simp [h2] at h_div
  -- h_div : shape.prod / shape[0] = shape.tail.prod
  exact h_div.symm

end algebra.ne_zero.ne_zero.then.eq.prod
open algebra.ne_zero.ne_zero.then.eq.prod
