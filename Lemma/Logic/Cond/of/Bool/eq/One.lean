import Lemma.Logic.Cond.is.Bool.eq.One
open Logic


@[main]
private lemma main
  [Decidable p]
-- given
  (h : Bool.toNat p = 1) :
-- imply
  p :=
-- proof
  Logic.Cond.is.Bool.eq.One.mpr h


-- created on 2025-04-11
