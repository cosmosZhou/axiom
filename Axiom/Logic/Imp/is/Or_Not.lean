import Axiom.Logic.Imp.is.OrNot
open Logic


@[main]
private lemma main:
-- imply
  (p → q ↔ q ∨ ¬p) := by
-- proof
  rw [Or.comm]
  rw [Imp.is.OrNot]


-- created on 2025-04-05
