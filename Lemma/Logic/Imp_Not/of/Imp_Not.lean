import Lemma.Logic.ImpNotS.of.Imp
import Lemma.Logic.IffNotNot
open Logic


@[main]
private lemma main
-- given
  (h : p → ¬q) :
-- imply
  q → ¬p := by
-- proof
  have := ImpNotS.of.Imp h
  rw [IffNotNot] at this
  assumption


-- created on 2025-04-14
