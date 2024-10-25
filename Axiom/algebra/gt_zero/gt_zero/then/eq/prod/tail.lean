import Mathlib.Tactic
import Axiom.algebra.gt.then.ne
import Axiom.algebra.ne_zero.ne_zero.then.eq.prod.tail
set_option linter.dupNamespace false

namespace algebra.gt_zero.gt_zero.then.eq.prod

theorem tail
  {shape : List ℕ}
-- given
  (h1: shape.length > 0)
  (h2: shape[0] > 0) :
-- imply
  shape.tail.prod = shape.prod / shape[0] := by
-- proof
  have h1' : shape.length ≠ 0 := by
    apply algebra.gt.then.ne h1

  have h2' : shape[0] ≠ 0 := by
    apply algebra.gt.then.ne h2

  apply algebra.ne_zero.ne_zero.then.eq.prod.tail h1' h2'


end algebra.gt_zero.gt_zero.then.eq.prod
open algebra.gt_zero.gt_zero.then.eq.prod
