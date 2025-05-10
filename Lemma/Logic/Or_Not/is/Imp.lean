import Lemma.Logic.Imp.is.Or_Not
open Logic


@[main]
private lemma main:
-- imply
  (p ∨ ¬q ↔ q → p) :=
-- proof
  Imp.is.Or_Not.symm


-- created on 2025-04-18
