import Lemma.Logic.Cond_Ite.is.OrAndS
open Logic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {x : α}
  {a b : β}
-- given
  (h : (R x a ∧ p) ∨ (R x b ∧ ¬p)) :
-- imply
  R x (if p then
    a
  else
    b) :=
-- proof
  Cond_Ite.is.OrAndS.mpr h


-- created on 2025-04-07
-- updated on 2025-04-11
