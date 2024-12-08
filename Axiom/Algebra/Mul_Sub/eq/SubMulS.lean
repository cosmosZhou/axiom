import Axiom.Algebra.SubMulS.eq.Mul_Sub

namespace Algebra.Mul_Sub.eq

theorem SubMulS
  [Ring α]
  {x a b : α} :
-- imply
  x * (a - b) = x * a - x * b := by
-- proof
  rw [SubMulS.eq.Mul_Sub]


end Algebra.Mul_Sub.eq

-- created on 2024-07-01
