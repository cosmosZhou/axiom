import Axiom.Algebra.Lt.to.Le.relax
import Axiom.Algebra.Le.Ge_0.to.LeMulS

namespace Algebra.Lt.Ge_0.to

theorem LeMulS
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a < b)
  (h2 : x ≥ 0) :
-- imply
  a * x ≤ b * x := by
-- proof
  have h := Lt.to.Le.relax h1
  apply Le.Ge_0.to.LeMulS h h2


end Algebra.Lt.Ge_0.to

-- created on 2024-07-01
