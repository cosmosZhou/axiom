import Axiom.Basic

namespace Algebra.Gt_0.Lt.to

theorem LtMulS
  [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
-- given
  (h1 : x > 0)
  (h2 : a < b) :
-- imply
  x * a < x * b := by
-- proof
  exact mul_lt_mul_of_pos_left h2 h1


end Algebra.Gt_0.Lt.to

-- created on 2024-07-01
