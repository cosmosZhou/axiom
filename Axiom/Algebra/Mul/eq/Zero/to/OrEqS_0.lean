import Axiom.Algebra.Eq_.Mul.Zero.equ.OrEqS_0

namespace Algebra.Mul.eq.Zero.to

theorem OrEqS_0
  [MulZeroClass α] [NoZeroDivisors α]
  {a b : α}
-- given
  (h : a * b = 0) :
-- imply
  a = 0 ∨ b = 0 := by
-- proof
  exact Eq_.Mul.Zero.equ.OrEqS_0.mp h


end Algebra.Mul.eq.Zero.to

-- created on 2024-11-29
