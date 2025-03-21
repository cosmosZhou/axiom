import Axiom.Algebra.And_Or.equ.OrAndS
open Algebra


@[main]
private lemma main
  (left : Bool := true) :
-- imply
  match left with
  | true => p ∧ q ∨ p ∧ r ↔ p ∧ (q ∨ r)
  | false => p ∧ q ∨ r ∧ p ↔ p ∧ (q ∨ r) := by
-- proof
  cases left with
  | true =>
    apply And_Or.equ.OrAndS.symm
  | false =>
    rw [And.comm (b := p)]
    apply And_Or.equ.OrAndS.symm


-- created on 2024-07-01
