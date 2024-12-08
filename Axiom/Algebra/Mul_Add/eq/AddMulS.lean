import Axiom.Algebra.AddMulS.eq.Mul_Add

namespace Algebra.Mul_Add.eq

theorem AddMulS
  [Mul α] [Add α] [LeftDistribClass α]
  {x a b : α} :
-- imply
  x * (a + b) = x * a + x * b := by
-- proof
  rw [AddMulS.eq.Mul_Add]


end Algebra.Mul_Add.eq

-- created on 2024-07-01
