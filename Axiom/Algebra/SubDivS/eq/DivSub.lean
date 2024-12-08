import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.SubMulS.eq.MulSub

namespace Algebra.SubDivS.eq

theorem DivSub
  [Field α]
  {x y a : α} :
-- imply
  x / a - y / a = (x - y) / a := by
-- proof
  rw [
    Div.eq.Mul_Inv,
    Div.eq.Mul_Inv,
    Div.eq.Mul_Inv,
    SubMulS.eq.MulSub
  ]


end Algebra.SubDivS.eq

-- created on 2024-07-01
