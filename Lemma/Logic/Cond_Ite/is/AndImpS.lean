import Lemma.Logic.AndImpS.of.Cond_Ite
import Lemma.Logic.Cond_Ite.of.AndImpS
open Logic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {x : α}
  {a b : β} :
-- imply
  (R x (if p then
    a
  else
    b)) ↔ (p → R x a) ∧ (¬p → R x b) :=
-- proof
  ⟨AndImpS.of.Cond_Ite, Cond_Ite.of.AndImpS⟩


-- created on 2025-01-12
-- updated on 2025-04-11
