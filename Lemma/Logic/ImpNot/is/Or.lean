import Lemma.Logic.Imp.is.OrNot
open Logic


@[main]
private lemma main :
-- imply
  (¬p → q ↔ p ∨ q)  := by
-- proof
  rw [Imp.is.OrNot]
  simp


-- created on 2025-01-12
