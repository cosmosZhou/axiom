import Axiom.Logic.OrNot.of.Imp
open Logic


@[main]
private lemma main
  {p q : Prop}
-- given
  (h : p → q) :
-- imply
  q ∨ ¬p := by
-- proof
  have := OrNot.of.Imp h
  rw [Or.comm]
  assumption


-- created on 2025-04-11
