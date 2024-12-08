import Axiom.Algebra.Gt_0.Lt.to.LtMulS

namespace Algebra.Gt_0.Gt.to

theorem GtMulS
  [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
-- given
  (h1 : x > 0)
  (h2 : a > b) :
-- imply
  x * a > x * b :=
-- proof
  Gt_0.Lt.to.LtMulS h1 h2


end Algebra.Gt_0.Gt.to

-- created on 2024-07-01
