import Lemma.Logic.AndOr.is.OrAndS
open Logic


@[main]
private lemma main
-- given
  (h : (q ∧ p) ∨ (r ∧ p)) :
-- imply
   (q ∨ r) ∧ p :=
-- proof
  AndOr.is.OrAndS.mpr h


-- created on 2025-04-07
