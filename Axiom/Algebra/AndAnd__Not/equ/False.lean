import Axiom.Algebra.AndAnd.equ.And_And
open Algebra


@[simp, main]
private lemma main
  {p q : Prop}
  (left : Bool := true) :
-- imply
  match left with
  | true =>
    (p ∧ q) ∧ ¬p ↔ False
  | false =>
    (q ∧ p) ∧ ¬p ↔ False
  := by
-- proof
  cases left with
  | true =>
    rw [And.comm (b := q)]
    rw [AndAnd.equ.And_And]
    simp
  | false =>
    rw [AndAnd.equ.And_And]
    simp


-- created on 2024-07-01
