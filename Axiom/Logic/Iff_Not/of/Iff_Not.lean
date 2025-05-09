import Axiom.Logic.IffNotS.of.Iff
open Logic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p ↔ ¬q) :
-- imply
  q ↔ ¬p := by
-- proof
  have h := IffNotS.of.Iff h
  simp at h
  exact h.symm


-- created on 2024-07-01
