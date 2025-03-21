import Axiom.Algebra.Imply.equ.OrNot
import Axiom.Algebra.NotAnd.equ.OrNotS
import Axiom.Algebra.OrOr.equ.Or_Or
open Algebra


@[main]
private lemma main :
-- imply
  p → q → r ↔ p ∧ q → r := by
-- proof
  rw [
    Imply.equ.OrNot,
    Imply.equ.OrNot,
    Imply.equ.OrNot,
    NotAnd.equ.OrNotS,
    OrOr.equ.Or_Or
  ]


-- created on 2024-07-01
