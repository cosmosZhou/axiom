import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Mul_Mul.eq.MulMul
import Axiom.Algebra.Mul.comm

namespace Algebra.SquareMul.eq

theorem MulSquareS
  [Field α]
  {a b : α} :
-- imply
  (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
-- proof
  rw [
    Square.eq.Mul,
    Mul_Mul.eq.MulMul,
    Mul.comm (a := a * b),
    Mul_Mul.eq.MulMul,
    Mul.eq.Square,
    MulMul.eq.Mul_Mul,
    Mul.eq.Square
  ]

end Algebra.SquareMul.eq

-- created on 2024-07-01
