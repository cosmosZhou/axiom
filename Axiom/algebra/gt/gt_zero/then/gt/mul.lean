import Mathlib.Tactic
import Axiom.algebra.gt.then.lt.reverse
import Axiom.algebra.lt.gt_zero.then.lt.mul

namespace algebra.gt.gt_zero.then.gt

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α]
  {x a b : α}
-- given
  (h1 : a > b)
  (h2 : x > 0):
-- imply
  a * x > b * x := by
-- proof
  have h := algebra.gt.then.lt.reverse h1
  apply algebra.lt.gt_zero.then.lt.mul h h2


end algebra.gt.gt_zero.then.gt
open algebra.gt.gt_zero.then.gt
