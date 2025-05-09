import Axiom.Logic.ImpNotS.of.Imp
open Logic


@[main]
private lemma main
-- given
  (h : ¬p → ¬q) :
-- imply
  q → p := by
-- proof
  have h := ImpNotS.of.Imp h
  simp at h
  exact h


-- created on 2024-07-01
