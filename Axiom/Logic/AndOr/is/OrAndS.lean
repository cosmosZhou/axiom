import Axiom.Logic.And_Or.is.OrAndS
open Logic


@[main]
private lemma main :
-- imply
  (q ∨ r) ∧ p ↔ q ∧ p ∨ r ∧ p := by
-- proof
  rw [And.comm]
  rw [And_Or.is.OrAndS]
  rw [And.comm]
  rw [And.comm (b := r)]


-- created on 2024-07-01
