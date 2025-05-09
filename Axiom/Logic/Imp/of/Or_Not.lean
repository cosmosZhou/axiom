import Axiom.Logic.Imp.of.OrNot
open Logic


@[main]
private lemma main
-- given
  (h : p ∨ ¬q) :
-- imply
  q → p := by
-- proof
  apply Imp.of.OrNot
  rw [Or.comm]
  assumption


-- created on 2025-04-09
