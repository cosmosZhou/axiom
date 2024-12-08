import Axiom.Basic

namespace Algebra.AddMulS.eq

theorem Mul_Add
  [Mul α] [Add α] [LeftDistribClass α]
  {x a b : α} :
-- imply
  x * a + x * b = x * (a + b) := by
-- proof
  rw [mul_add]


end Algebra.AddMulS.eq

-- created on 2024-07-01
