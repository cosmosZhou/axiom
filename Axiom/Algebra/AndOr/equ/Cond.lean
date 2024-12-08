import Axiom.Algebra.AndOr.equ.OrAndS


namespace Algebra.AndOr.equ

theorem Cond
-- imply
  (right : Bool := true) :
  match right with
  | true => (q ∨ p) ∧ p ↔ p
  | false => (p ∨ q) ∧ p ↔ p := by
-- proof
  simp [AndOr.equ.OrAndS]

  cases right
  case true =>
    simp
  case false =>
    simp



end Algebra.AndOr.equ

-- created on 2024-07-01
