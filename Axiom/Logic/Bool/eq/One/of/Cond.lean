import Axiom.Logic.Cond.is.Bool.eq.One
open Logic


@[main]
private lemma main
  [Decidable p]
-- given
  (h : p) :
-- imply
  Bool.toNat p = 1 :=
-- proof
  Logic.Cond.is.Bool.eq.One.mp h


-- created on 2025-04-11
