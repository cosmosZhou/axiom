import Axiom.Algebra.Div_Mul.eq.DivDiv
import Axiom.Algebra.Mul.comm

namespace Algebra.Ne_0.to.Eq_.Div_Mul

lemma inv'
  [Field α]
  {a b : α}
-- given
  (h : a ≠ 0) :
-- imply
  a / (a * b) = b⁻¹ := by
  rw [Div_Mul.eq.DivDiv]
  simp [h]


theorem Inv
  [Field α]
  {a b : α}
-- given
  (h : a ≠ 0)
  (comm : Bool := false) :
-- imply
  match comm with
  | true  =>
    a / (b * a) = b⁻¹
  | false =>
    a / (a * b) = b⁻¹ := by
-- proof
  cases comm
  case true  =>
    simp
    rw [Mul.comm]
    apply inv' h

  case false =>
    simp
    apply inv' h


end Algebra.Ne_0.to.Eq_.Div_Mul

-- created on 2024-07-01
