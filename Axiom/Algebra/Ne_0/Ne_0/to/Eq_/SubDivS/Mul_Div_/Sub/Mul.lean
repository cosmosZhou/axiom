import Axiom.Algebra.Div.eq.Mul_Inv
import Axiom.Algebra.SubMulS.eq.Mul_Sub
import Axiom.Algebra.Ne_0.Ne_0.to.Eq_.SubInvS.Div_.Sub.Mul

namespace Algebra.Ne_0.Ne_0.to.Eq_.SubDivS.Mul_Div_.Sub

theorem Mul
  [Field α]
  {x a b : α}
  (h0 : a ≠ 0)
  (h1 : b ≠ 0) :
-- imply
  x / a - x / b = x * ((b - a) / (a * b)) := by
-- proof
  rw [
    Div.eq.Mul_Inv,
    Div.eq.Mul_Inv,
    SubMulS.eq.Mul_Sub,
    Ne_0.Ne_0.to.Eq_.SubInvS.Div_.Sub.Mul h0 h1
  ]


end Algebra.Ne_0.Ne_0.to.Eq_.SubDivS.Mul_Div_.Sub

-- created on 2024-07-01
