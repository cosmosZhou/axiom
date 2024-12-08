import Axiom.Algebra.Ge_0.Le.to.LeMulS

namespace Algebra.Ge_0.Ge.to

theorem GeMulS
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h1 : x ≥ 0)
  (h2 : a ≥ b) :
-- imply
  x * a ≥ x * b :=
-- proof
  Ge_0.Le.to.LeMulS h1 h2


end Algebra.Ge_0.Ge.to

-- created on 2024-07-01
