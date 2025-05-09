import Axiom.Logic.AndAnd.is.And_And
open Logic


@[main]
private lemma main:
-- imply
  (p ∧ q) ∧ r ↔ (p ∧ r) ∧ q := by
-- proof
  rw [AndAnd.is.And_And]
  rw [AndAnd.is.And_And]
  rw [And.comm (a := q)]


-- created on 2025-04-18
