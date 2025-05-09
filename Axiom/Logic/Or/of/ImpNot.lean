import Axiom.Logic.Imp.is.OrNot
import Axiom.Logic.IffNotNot
open Logic


@[main]
private lemma main
-- given
  (h : ¬p → q) :
-- imply
  p ∨ q := by
-- proof
  rw [Imp.is.OrNot] at h
  rw [IffNotNot] at h
  assumption


-- created on 2025-04-05
