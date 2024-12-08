import Axiom.Algebra.Gt.to.Ge.relax
import Axiom.Algebra.Ge_0.Le.to.LeMulS

namespace Algebra.Gt_0.Le.to

theorem LeMulS
  {α : Type*} [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x > 0)
  (h2 : a ≤ b) :
-- imply
  x * a ≤ x * b := by
-- proof
  have h := Gt.to.Ge.relax h1
  apply Ge_0.Le.to.LeMulS h h2


end Algebra.Gt_0.Le.to

-- created on 2024-07-01
