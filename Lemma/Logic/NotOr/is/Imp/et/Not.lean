import Lemma.Logic.Imp.et.Not.is.NotOr
open Logic


@[main]
private lemma main:
-- imply
  ¬(p ∨ q) ↔ (q → p) ∧ ¬p :=
-- proof
  Imp.et.Not.is.NotOr.symm


-- created on 2025-04-09
