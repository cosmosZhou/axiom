import Axiom.Algebra.Gt.to.Ge.relax
import Axiom.Algebra.Ge_0.Ge.to.GeMulS

namespace Algebra.Ge_0.Gt.to

theorem GeMulS
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x ≥ 0)
  (h2 : a > b) :
-- imply
  x * a ≥ x * b := by
-- proof
  have h := Gt.to.Ge.relax h2
  apply Ge_0.Ge.to.GeMulS h1 h


end Algebra.Ge_0.Gt.to

-- created on 2024-07-01
