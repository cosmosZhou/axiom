import Axiom.Algebra.AndNotS.of.NotOr
import Axiom.Algebra.NotOr.of.AndNotS
open Algebra


@[main]
private lemma main :
-- imply
  ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
-- proof
  ⟨AndNotS.of.NotOr, NotOr.of.AndNotS⟩


-- created on 2024-07-01
