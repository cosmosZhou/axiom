import Axiom.Logic.Cond.is.Bool.eq.One
open Logic


@[main]
private lemma main
  [Decidable p] :
-- imply
  Bool.toNat p = 1 ↔ p :=
-- proof
  Cond.is.Bool.eq.One.symm


-- created on 2025-04-11
-- updated on 2025-04-20
