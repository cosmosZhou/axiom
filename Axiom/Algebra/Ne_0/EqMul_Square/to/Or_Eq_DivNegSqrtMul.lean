import Axiom.sympy.core.numbers
import Axiom.Algebra.Eq.to.EqDivS
import Axiom.Algebra.EqSquare.to.Or_Eq_NegSqrt
import Axiom.Algebra.NegDiv.eq.DivNeg

namespace Algebra.Ne_0.EqMul_Square.to

theorem Or_Eq_DivNegSqrtMul
  {x a b c : ℂ}
-- given
  (h0 : a ≠ 0)
  (h1 : a * x ^ 2 = c) :
-- imply
  x = √(a * c) / a ∨
  x = -√(a * c) / a := by
-- proof
  have h1 := Eq.to.EqDivS h1 a

  simp [h0] at h1

  have h := EqSquare.to.Or_Eq_NegSqrt h1

  have h: √c = exp (log √c) := by
    simp
  have h_eq_sqrt : √(c / a) = √c / √a := by
    simp [Root.sqrt]


  have h_eq : √(a * c) / a = √(c / a) := by
    sorry


  rw [
    h_eq.symm,
    NegDiv.eq.DivNeg
  ] at h

  exact h



end Algebra.Ne_0.EqMul_Square.to

-- created on 2024-07-01
