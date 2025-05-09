import Axiom.Logic.NotAnd.of.OrNotS
import Axiom.Logic.OrNotS.of.NotAnd
open Logic


@[main]
private lemma main :
-- imply
  ¬p ∨ ¬q ↔ ¬(p ∧ q) :=
-- proof
  ⟨NotAnd.of.OrNotS,  OrNotS.of.NotAnd⟩


-- created on 2024-07-01
