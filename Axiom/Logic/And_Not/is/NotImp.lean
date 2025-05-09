import Axiom.Logic.NotImp.is.And_Not
open Logic


@[main]
private lemma main :
-- imply
  p ∧ ¬q ↔ ¬(p → q) :=
-- proof
  NotImp.is.And_Not.symm


-- created on 2024-07-01
