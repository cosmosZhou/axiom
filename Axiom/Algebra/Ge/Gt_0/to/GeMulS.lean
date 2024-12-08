import Axiom.Algebra.Gt.to.Ge.relax
import Axiom.Algebra.Ge.Ge_0.to.GeMulS

namespace Algebra.Ge.Gt_0.to

theorem GeMulS
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a ≥ b)
  (h2 : x > 0) :
-- imply
  a * x ≥ b * x := by
-- proof
  have h := Gt.to.Ge.relax h2
  apply Ge.Ge_0.to.GeMulS h1 h

end Algebra.Ge.Gt_0.to

-- created on 2024-07-01
