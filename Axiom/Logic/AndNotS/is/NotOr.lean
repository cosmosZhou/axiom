import Axiom.Logic.NotOr.is.AndNotS
open Logic


@[main]
private lemma main:
-- imply
  ¬p ∧ ¬q ↔ ¬(p ∨ q) :=
-- proof
  NotOr.is.AndNotS.symm


-- created on 2025-04-08
