import Axiom.Algebra.IffNotS.of.Iff
open Algebra


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
