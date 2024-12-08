import Axiom.sympy.core.numbers
import Axiom.Algebra.Eq_.AddMul.Zero.to.And_Imply_Eq_DivNeg.simple
import Axiom.Algebra.Ne_0.Eq_.Add_.Mul_Square.Mul.Zero.to.Or_Eq_Div_.Sub_Sqrt.Mul2

namespace Algebra.Eq_.Add_.Mul_Square.Mul.Zero.to.And_Imply_Eq_Div_.Sub_Sqrt

theorem Mul2
  {x a b c : ℂ}
-- given
  (h : a * x ^ 2 + b * x + c = 0) :
-- imply
  (a = 0 ∧ b = 0 → c = 0) ∧
  (a = 0 ∧ b ≠ 0 → x = -c / b) ∧
  (a ≠ 0 →
    let δ : ℂ := b ^ 2 - 4 * a * c
    (x = (-b + √δ) / (2 * a) ∨
    x = (-b - √δ) / (2 * a))
  ) := by
-- proof
  constructor
  -- case left
  intro ha
  rw [ha.left] at h
  rw [ha.right] at h
  simp at h
  exact h

  -- case right
  constructor
  -- case right.left
  intro ha
  rw [ha.left] at h
  simp at h
  exact (Eq_.AddMul.Zero.to.And_Imply_Eq_DivNeg.simple h).right ha.right

  -- case right.right
  intro ha
  apply Ne_0.Eq_.Add_.Mul_Square.Mul.Zero.to.Or_Eq_Div_.Sub_Sqrt.Mul2 ha h


end Algebra.Eq_.Add_.Mul_Square.Mul.Zero.to.And_Imply_Eq_Div_.Sub_Sqrt

-- created on 2024-07-01
