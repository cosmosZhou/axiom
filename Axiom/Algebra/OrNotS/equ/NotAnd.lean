import Axiom.Algebra.NotAnd.of.OrNotS
import Axiom.Algebra.OrNotS.of.NotAnd
open Algebra


@[main]
private lemma main :
-- imply
  ¬p ∨ ¬q ↔ ¬(p ∧ q) :=
-- proof
  ⟨NotAnd.of.OrNotS,  OrNotS.of.NotAnd⟩


-- created on 2024-07-01
