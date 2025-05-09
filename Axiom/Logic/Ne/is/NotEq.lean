import Axiom.Logic.NotEq.is.Ne
open Logic


@[main]
private lemma main
  {a b : α} :
-- imply
  a ≠ b ↔ (¬a = b) :=
-- proof
  NotEq.is.Ne.symm


-- created on 2025-04-20
