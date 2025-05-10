import Lemma.Logic.Cond_Ite__Ite.is.And.ou.OrAndS
open Logic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {R : α → β → Prop}
  {x : α}
  {a b c : β}
-- given
  (h : (R x a ∧ p) ∨ (R x b ∧ q ∧ ¬p) ∨ (R x c ∧ ¬(p ∨ q))) :
-- imply
  R x (if p then
    a
  else if q then
    b
  else
    c) :=
-- proof
  Cond_Ite__Ite.is.And.ou.OrAndS.mpr h


-- created on 2025-04-08
-- updated on 2025-04-11
