import Axiom.Algebra.NotImply.equ.And_Not
open Algebra


@[main]
private lemma main :
-- imply
  p ∧ ¬q ↔ ¬(p → q) :=
-- proof
  NotImply.equ.And_Not.symm


-- created on 2024-07-01
