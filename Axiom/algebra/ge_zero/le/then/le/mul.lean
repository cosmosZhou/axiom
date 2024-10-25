import Mathlib.Tactic

namespace algebra.ge_zero.le.then.le

theorem mul
  {α : Type*} [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x ≥ 0)
  (h2 : a ≤ b):
-- imply
  x * a ≤ x * b := by
-- proof
  exact mul_le_mul_of_nonneg_left h2 h1


end algebra.ge_zero.le.then.le
open algebra.ge_zero.le.then.le
