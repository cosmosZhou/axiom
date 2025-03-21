import Axiom.Algebra.OrAndS.equ.And_Or
open Algebra


@[main]
private lemma main
  (right : Bool := true) :
-- imply
  match right with
  | true => q ∧ p ∨ r ∧ p ↔ (q ∨ r) ∧ p
  | false => p ∧ q ∨ r ∧ p ↔ (q ∨ r) ∧ p := by
-- proof
  cases right with
  | true =>
    simp
    rw [And.comm (b := p)]
    simp [OrAndS.equ.And_Or false]
    rw [And.comm]
  | false =>
    simp
    simp [OrAndS.equ.And_Or false]
    rw [And.comm]


-- created on 2024-07-01
