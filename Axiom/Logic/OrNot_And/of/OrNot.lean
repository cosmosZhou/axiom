import Axiom.Logic.Or_AndNot.of.Or
import Axiom.Logic.IffNotNot
open Logic


@[main]
private lemma main
-- given
  (h : ¬p ∨ q) :
-- imply
  ¬p ∨ (p ∧ q) := by
-- proof
  have := Or_AndNot.of.Or h
  rw [IffNotNot] at this
  assumption


-- created on 2025-04-07
