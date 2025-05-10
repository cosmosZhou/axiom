import Lemma.Logic.Cond_Ite.is.OrAndS
open Logic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {x : α}
  {a b : β}
-- given
  (h : R x (if p then
    a
  else
    b)) :
-- imply
  (R x a ∧ p) ∨ (R x b ∧ ¬p) :=
-- proof
  Cond_Ite.is.OrAndS.mp h


-- created on 2025-04-08
-- updated on 2025-04-11
