import Axiom.Algebra.Mul.eq.Square
import Axiom.Algebra.Mul_Div.eq.DivMul
import Axiom.Algebra.MulDiv.eq.DivMul
import Axiom.Algebra.DivDiv.eq.Div_Mul

namespace Algebra.SquareDiv.eq


theorem DivSquareS
  [Field α]
  {a b : α} :
-- imply
  (a / b) ^ 2 = a ^ 2 / b ^ 2 := by
-- proof
  rw [
    Square.eq.Mul,
    Mul_Div.eq.DivMul,
    MulDiv.eq.DivMul,
    Mul.eq.Square,
    DivDiv.eq.Div_Mul,
    Mul.eq.Square
  ]


end Algebra.SquareDiv.eq

-- created on 2024-07-01
