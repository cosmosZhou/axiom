import Axiom.Logic.OrNotS.is.NotAnd
open Logic


@[main]
private lemma main :
-- imply
  ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
-- proof
  OrNotS.is.NotAnd.symm


-- created on 2024-07-01
