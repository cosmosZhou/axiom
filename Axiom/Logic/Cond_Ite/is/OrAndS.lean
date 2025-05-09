import Axiom.Logic.Cond_Ite.is.AndImpS
import Axiom.Logic.Imp.is.OrNot
import Axiom.Logic.ImpNot.is.Or
import Axiom.Logic.OrAndS.of.Or.Or
import Axiom.Logic.Or.of.OrAndS
import Axiom.Logic.OrNot.of.OrAndS
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
