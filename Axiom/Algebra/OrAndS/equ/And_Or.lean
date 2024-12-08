import Axiom.Algebra.And_Or.equ.OrAndS

namespace Algebra.OrAndS.equ

theorem And_Or
  (left : Bool := true) :
-- imply
  match left with
  | true => p ∧ q ∨ p ∧ r ↔ p ∧ (q ∨ r)
  | false => p ∧ q ∨ r ∧ p ↔ p ∧ (q ∨ r) := by
-- proof
  cases left
  case true =>
    apply And_Or.equ.OrAndS.symm
  case false =>
    rw [And.comm (b := p)]
    apply And_Or.equ.OrAndS.symm


end Algebra.OrAndS.equ

-- created on 2024-07-01
