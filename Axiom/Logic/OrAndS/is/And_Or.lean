import Axiom.Logic.And_Or.is.OrAndS
open Logic


@[main]
private lemma left:
-- imply
  p ∧ q ∨ p ∧ r ↔ p ∧ (q ∨ r) :=
-- proof
  And_Or.is.OrAndS.symm


@[main]
private lemma main:
-- imply
  p ∧ q ∨ r ∧ p ↔ p ∧ (q ∨ r) := by
-- proof
  rw [And.comm (b := p)]
  apply And_Or.is.OrAndS.symm


-- created on 2024-07-01
