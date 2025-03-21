import Axiom.Algebra.OrNotS.equ.NotAnd
open Algebra


@[main]
private lemma main :
-- imply
  ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
-- proof
  OrNotS.equ.NotAnd.symm


-- created on 2024-07-01
