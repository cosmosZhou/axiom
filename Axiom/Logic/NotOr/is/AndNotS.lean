import Axiom.Logic.AndNotS.of.NotOr
import Axiom.Logic.NotOr.of.AndNotS
open Logic


@[main]
private lemma main :
-- imply
  ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
-- proof
  ⟨AndNotS.of.NotOr, NotOr.of.AndNotS⟩


-- created on 2024-07-01
