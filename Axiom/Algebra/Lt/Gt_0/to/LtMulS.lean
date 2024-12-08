import Axiom.Basic

namespace Algebra.Lt.Gt_0.to

theorem LtMulS
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α]
  {x a b : α}
-- given
  (h1 : a < b)
  (h2 : x > 0) :
-- imply
  a * x < b * x := by
-- proof
  exact mul_lt_mul_of_pos_right h1 h2

end Algebra.Lt.Gt_0.to

-- created on 2024-07-01
