import Axiom.Logic.OrAndS.is.And_Or
open Logic


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
    simp [OrAndS.is.And_Or]
    rw [And.comm]
  | false =>
    simp
    simp [OrAndS.is.And_Or]
    rw [And.comm]


-- created on 2024-07-01
-- updated on 2025-04-21
