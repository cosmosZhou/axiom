import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.SubDivS.eq.DivSub
import Axiom.Algebra.DivMul.eq.Mul_Div
import Axiom.Algebra.Ne_0.to.Eq_.Div_Mul.Inv

namespace Algebra.Ne_0.Ne_0.to.SubDivS.eq.Div_.SubMulS

theorem Mul
  [Field α]
  {a b x y : α}
  (h0 : a ≠ 0)
  (h1 : b ≠ 0) :
-- imply
  x / a - y / b = (x * b - y * a) / (a * b) := by
-- proof
  rw [
    Div.eq.Mul_Inv,
    Div.eq.Mul_Inv,
    ← SubDivS.eq.DivSub,
    DivMul.eq.Mul_Div,
    Ne_0.to.Eq_.Div_Mul.Inv h1 true,

    DivMul.eq.Mul_Div,
    Ne_0.to.Eq_.Div_Mul.Inv h0
  ]


end Algebra.Ne_0.Ne_0.to.SubDivS.eq.Div_.SubMulS

-- created on 2024-07-01
