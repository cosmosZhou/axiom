import Mathlib.Tactic
import Axiom.sympy.core.containers.list
import Axiom.algebra.sum.cons.to.add.sum

namespace algebra.is_uniform.then.eq_dot.mul

theorem sum
  [DecidableEq α] [AddMonoid α] [MulZeroClass α]
  {s s' : List α}
-- given
  (h: s is uniform):
-- imply
  s'.dot s = s'.sum * s.headD 0 := by
  sorry


end algebra.is_uniform.then.eq_dot.mul
open algebra.is_uniform.then.eq_dot.mul
