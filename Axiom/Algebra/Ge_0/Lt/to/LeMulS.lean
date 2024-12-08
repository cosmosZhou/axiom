import Axiom.Algebra.Lt.to.Le.relax
import Axiom.Algebra.Ge_0.Le.to.LeMulS

namespace Algebra.Ge_0.Lt.to

theorem LeMulS
  {α : Type*} [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x ≥ 0)
  (h2 : a < b) :
-- imply
  x * a ≤ x * b := by
-- proof
  have h := Lt.to.Le.relax h2
  apply Ge_0.Le.to.LeMulS h1 h


end Algebra.Ge_0.Lt.to

-- created on 2024-07-01
