import Lemma.Logic.Cond_Ite.is.AndImpS
import Lemma.Logic.Imp.is.OrNot
import Lemma.Logic.ImpNot.is.Or
import Lemma.Logic.OrAndS.of.Or.Or
import Lemma.Logic.Or.of.OrAndS
import Lemma.Logic.OrNot.of.OrAndS
open Logic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {x : α}
  {a b : β} :
-- imply
  (R x (if p then a else b)) ↔ R x a ∧ p ∨ R x b ∧ ¬p := by
-- proof
  rw [Cond_Ite.is.AndImpS (R := R)]
  rw [Imp.is.OrNot]
  rw [ImpNot.is.Or]
  constructor
  intro h
  apply OrAndS.of.Or.Or h.left h.right
  intro h
  exact And.intro (OrNot.of.OrAndS h) (Or.of.OrAndS h)


-- created on 2025-01-12
-- updated on 2025-04-11
