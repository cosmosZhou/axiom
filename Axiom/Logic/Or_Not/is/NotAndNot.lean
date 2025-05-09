import Axiom.Logic.NotAnd.is.OrNotS
import Axiom.Logic.IffNotNot
open Logic


@[main]
private lemma main:
-- imply
  p ∨ ¬q ↔ ¬(¬p ∧ q) := by
-- proof
  rw [NotAnd.is.OrNotS]
  rw [IffNotNot]


-- created on 2025-04-12
