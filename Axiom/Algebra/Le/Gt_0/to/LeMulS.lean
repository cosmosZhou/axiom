import Axiom.Algebra.Gt.to.Ge.relax
import Axiom.Algebra.Le.Ge_0.to.LeMulS

namespace Algebra.Le.Gt_0.to

theorem LeMulS
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a ≤ b)
  (h2 : x > 0) :
-- imply
  a * x ≤ b * x :=
-- proof
  Le.Ge_0.to.LeMulS h1 (Gt.to.Ge.relax h2)

end Algebra.Le.Gt_0.to

-- created on 2024-07-01
