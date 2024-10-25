import Mathlib.Tactic
import Axiom.algebra.gt.then.ge.relax
import Axiom.algebra.le.ge_zero.then.le.mul

namespace algebra.le.gt_zero.then.le

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a ≤ b)
  (h2 : x > 0):
-- imply
  a * x ≤ b * x := by
-- proof
  have h := algebra.gt.then.ge.relax h2
  apply algebra.le.ge_zero.then.le.mul h1 h

end algebra.le.gt_zero.then.le
open algebra.le.gt_zero.then.le
