import Lemma.Logic.Imp.of.Cond_Ite
import Lemma.Logic.ImpNot.of.Cond_Ite
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
  (p → R x a) ∧ (¬p → R x b) := by
-- proof
  constructor
  apply Imp.of.Cond_Ite h
  apply ImpNot.of.Cond_Ite h


-- created on 2025-01-12
-- updated on 2025-04-11
