import Axiom.Logic.Cond_Ite.is.OrAndS
import Axiom.Logic.Any_Iff
open Logic


@[main]
private lemma main
  [Decidable p]
  {R : β → α → Prop}
  {x : α}
  {a b : β} :
-- imply
  (R (if p then
    a
  else
    b) x) ↔ R a x ∧ p ∨ R b x ∧ ¬p := by
-- proof
  let ⟨_, h_Iff⟩ := Any_Iff (R := R)
  rw [h_Iff, h_Iff, h_Iff] at *
  apply Cond_Ite.is.OrAndS


-- created on 2025-04-12
