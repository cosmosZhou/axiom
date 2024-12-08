import Axiom.Algebra.OrAndS.equ.And_Or

namespace Algebra.OrAndS.equ

theorem AndOr
  (right : Bool := true) :
-- imply
  match right with
  | true => q ∧ p ∨ r ∧ p ↔ (q ∨ r) ∧ p
  | false => p ∧ q ∨ r ∧ p ↔ (q ∨ r) ∧ p := by
-- proof
  cases right
  case true =>
    simp
    rw [And.comm (b := p)]
    simp [OrAndS.equ.And_Or false]
    rw [And.comm]
  case false =>
    simp
    simp [OrAndS.equ.And_Or false]
    rw [And.comm]


end Algebra.OrAndS.equ

-- created on 2024-07-01
