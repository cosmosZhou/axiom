import Axiom.Algebra.AndOr.equ.Cond
open Algebra


@[main]
private lemma main
  (left : Bool := false) :
-- imply
  match left with
  | true => p ∧ (p ∨ q) ↔ p
  | false => p ∧ (q ∨ p) ↔ p := by
-- proof
  rw [And.comm]
  rw [And.comm (a := p)]
  cases left with
  | true =>
    apply AndOr.equ.Cond false
  | false =>
    apply AndOr.equ.Cond true


-- created on 2024-07-01
