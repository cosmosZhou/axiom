import Lemma.Logic.OrOr.is.Or_Or
open Logic


@[main]
private lemma main :
-- imply
  p ∨ q ∨ r ↔ (p ∨ q) ∨ r :=
-- proof
  OrOr.is.Or_Or.symm


-- created on 2024-07-01
