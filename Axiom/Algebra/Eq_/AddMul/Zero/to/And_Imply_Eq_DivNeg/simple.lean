import Axiom.Algebra.Eq_.Add.Zero.to.Eq_Neg
import Axiom.Algebra.Eq.to.EqDivS
import Axiom.Algebra.Ne_0.EqMul.to.Eq_Div

namespace Algebra.Eq_.AddMul.Zero.to.And_Imply_Eq_DivNeg


theorem simple
  [Field α]
  {x a b : α}
-- given
  (h : a * x + b = 0) :
-- imply
  (a = 0 → b = 0) ∧
  (a ≠ 0 → x = -b / a) := by
-- proof
  constructor
  -- case left
  intro ha
  rw [ha] at h
  simp at h
  exact h

  -- case right
  intro ha

  have h: a * x = -b := Eq_.Add.Zero.to.Eq_Neg h

  have h: x = -b / a := Ne_0.EqMul.to.Eq_Div (left := true) ha h

  exact h



end Algebra.Eq_.AddMul.Zero.to.And_Imply_Eq_DivNeg

-- created on 2024-07-01
