import Axiom.Algebra.MulMul.eq.Mul_Mul

namespace Algebra.Mul_Mul.eq

theorem MulMul
  [Semigroup α]
  {a b : α} :
-- imply
  a * (b * c) = a * b * c := by
-- proof
  rw [MulMul.eq.Mul_Mul]


end Algebra.Mul_Mul.eq

-- created on 2024-07-01
