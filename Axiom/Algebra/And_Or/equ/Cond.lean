import Axiom.Algebra.AndOr.equ.Cond


namespace Algebra.And_Or.equ

theorem Cond
-- imply
  (left : Bool := false) :
  match left with
  | true => p ∧ (p ∨ q) ↔ p
  | false => p ∧ (q ∨ p) ↔ p := by
-- proof
  rw [And.comm]
  rw [And.comm (a := p)]

  cases left
  case true =>
    apply AndOr.equ.Cond false
  case false =>
    apply AndOr.equ.Cond true


end Algebra.And_Or.equ

-- created on 2024-07-01
