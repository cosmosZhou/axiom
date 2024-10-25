import Mathlib.Tactic
import Axiom.algebra.gt.then.lt.reverse
import Axiom.algebra.gt_zero.lt.then.lt.mul
import Axiom.algebra.lt.then.gt.reverse

namespace algebra.gt_zero.gt.then.gt

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
-- given
  (h1 : x > 0)
  (h2 : a > b):
-- imply
  x * a > x * b := by
-- proof
  have h := algebra.gt.then.lt.reverse h2
  have h := algebra.gt_zero.lt.then.lt.mul h1 h
  apply algebra.lt.then.gt.reverse h


end algebra.gt_zero.gt.then.gt
open algebra.gt_zero.gt.then.gt
