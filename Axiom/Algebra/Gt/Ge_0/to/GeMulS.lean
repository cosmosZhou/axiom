import Axiom.Algebra.Gt.to.Ge.relax
import Axiom.Algebra.Ge.Ge_0.to.GeMulS

namespace Algebra.Gt.Ge_0.to

theorem GeMulS
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a > b)
  (h2 : x ≥ 0) :
-- imply
  a * x ≥ b * x := by
-- proof
  have h := Gt.to.Ge.relax h1
  apply Ge.Ge_0.to.GeMulS h h2


end Algebra.Gt.Ge_0.to

-- created on 2024-07-01
