import Axiom.Algebra.Lt.Gt_0.to.LtMulS

namespace Algebra.Gt.Gt_0.to

theorem GtMulS
  [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α]
  {x a b : α}
-- given
  (h1 : a > b)
  (h2 : x > 0) :
-- imply
  a * x > b * x := by
-- proof
  apply Lt.Gt_0.to.LtMulS h1 h2


end Algebra.Gt.Gt_0.to

-- created on 2024-07-01
