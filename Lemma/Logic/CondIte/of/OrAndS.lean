import Lemma.Logic.CondIte.is.OrAndS
open Logic


@[main]
private lemma main
  [Decidable p]
  {R : β → α → Prop}
  {x : α}
  {a b : β}
-- given
  (h : (R a x ∧ p) ∨ (R b x ∧ ¬p)) :
-- imply
  R (if p then
    a
  else
    b) x :=
-- proof
  CondIte.is.OrAndS.mpr h


-- created on 2025-04-12
