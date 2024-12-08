import Axiom.Basic

namespace Algebra.Le.Ge_0.to

theorem LeMulS
  {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h1 : a ≤ b)
  (h2 : x ≥ 0) :
-- imply
  a * x ≤ b * x :=
-- proof
  mul_le_mul_of_nonneg_right h1 h2


end Algebra.Le.Ge_0.to

-- created on 2024-07-01
