import Axiom.Algebra.AndAnd.equ.And_And

namespace Algebra.And_.And.Not.equ

@[simp]
theorem False
  {p q : Prop}
-- imply
  (left : Bool := true) :
  match left with
  | true =>
    (p ∧ q) ∧ ¬p ↔ False
  | false =>
    (q ∧ p) ∧ ¬p ↔ False
  := by
-- proof
  cases left
  case true =>
    rw [And.comm (b := q)]
    rw [AndAnd.equ.And_And]
    simp
  case false =>
    rw [AndAnd.equ.And_And]
    simp


end Algebra.And_.And.Not.equ

-- created on 2024-07-01
