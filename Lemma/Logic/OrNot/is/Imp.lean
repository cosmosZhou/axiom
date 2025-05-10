import Lemma.Logic.Imp.is.OrNot
open Logic


@[main]
private lemma main:
-- imply
  (¬p ∨ q ↔ p → q) :=
-- proof
  Imp.is.OrNot.symm


-- created on 2025-04-18
