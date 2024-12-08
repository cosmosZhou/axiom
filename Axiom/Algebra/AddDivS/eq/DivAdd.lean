import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.AddMulS.eq.MulAdd

namespace Algebra.AddDivS.eq

theorem DivAdd
  [Field α]
  {x y a : α} :
-- imply
  x / a + y / a = (x + y) / a := by
-- proof
  rw [
    Div.eq.Mul_Inv,
    Div.eq.Mul_Inv,
    Div.eq.Mul_Inv,
    AddMulS.eq.MulAdd
  ]


end Algebra.AddDivS.eq

-- created on 2024-07-01
