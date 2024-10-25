import Mathlib.Tactic

namespace algebra.le.ge_zero.then.le

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a ≤ b)
  (h2 : x ≥ 0):
-- imply
  a * x ≤ b * x := by
-- proof
  exact mul_le_mul_of_nonneg_right h1 h2


end algebra.le.ge_zero.then.le
open algebra.le.ge_zero.then.le
