import Axiom.Algebra.Eq.to.EqDivS

namespace Algebra.Ne_0.EqMul.to

theorem Eq_Div
  [Field α]
  {a c b : α}
  {left : Bool}
-- given
  (h_ne :
    match left with
    | true => a ≠ 0
    | false => b ≠ 0
  )
  (h : a * b = c) :
-- imply
  match left with
  | true => b = c / a
  | false => a = c / b := by
-- proof
  match left with
  | true =>
    have h := Eq.to.EqDivS h a

    have h_eq : a * b / a = b := by
      simp [h_ne]

    exact h_eq ▸ h
  | false =>
    have h := Eq.to.EqDivS h b
    have h_eq: a * b / b = a := by
      simp [h_ne]
    exact h_eq ▸ h


end Algebra.Ne_0.EqMul.to

-- created on 2024-07-01
