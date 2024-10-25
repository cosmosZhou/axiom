import Mathlib.Tactic

namespace algebra.gt_zero.lt.then.lt

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
-- given
  (h1 : x > 0)
  (h2 : a < b):
-- imply
  x * a < x * b := by
-- proof
  exact mul_lt_mul_of_pos_left h2 h1


end algebra.gt_zero.lt.then.lt
open algebra.gt_zero.lt.then.lt
