import Mathlib.Tactic

namespace algebra.lt.gt_zero.then.lt

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α]
  {x a b : α}
-- given
  (h1 : a < b)
  (h2 : x > 0):
-- imply
  a * x < b * x := by
-- proof
  exact mul_lt_mul_of_pos_right h1 h2

end algebra.lt.gt_zero.then.lt
open algebra.lt.gt_zero.then.lt
