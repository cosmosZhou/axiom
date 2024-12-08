import Axiom.Algebra.Div1.eq.Inv
import Axiom.Algebra.Ne_0.Ne_0.to.SubDivS.eq.Div_.SubMulS.Mul

namespace Algebra.Ne_0.Ne_0.to.Eq_.SubInvS.Div_.Sub

theorem Mul
  [Field α]
  {a b : α}
  (h0 : a ≠ 0)
  (h1 : b ≠ 0) :
-- imply
  a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
-- proof
  rw [
    ← Div1.eq.Inv,
    ← Div1.eq.Inv,
    Ne_0.Ne_0.to.SubDivS.eq.Div_.SubMulS.Mul h0 h1
  ]

  simp


end Algebra.Ne_0.Ne_0.to.Eq_.SubInvS.Div_.Sub

-- created on 2024-07-01
