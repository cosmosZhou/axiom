import Axiom.Logic.Cond_Ite__Ite.is.And.ou.OrAndS
open Logic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {S : Set α}
  {a b c : α}
-- given
  (h : (a ∈ S ∧ p) ∨ (b ∈ S ∧ q ∧ ¬p) ∨ (c ∈ S ∧ ¬(p ∨ q))) :
-- imply
  (if p then
    a
  else if q then
    b
  else
    c) ∈ S :=
-- proof
  Cond_Ite__Ite.is.And.ou.OrAndS.mpr h


-- created on 2025-04-18
