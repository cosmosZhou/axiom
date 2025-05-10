import Lemma.Logic.Cond_Ite.of.AndImpS
import Lemma.Logic.Any_Iff
open Logic


@[main]
private lemma main
  [Decidable p]
  {R : β → α → Prop}
  {x : α}
  {a b : β}
-- given
  (h : (p → R a x) ∧ (¬p → R b x)) :
-- imply
  R (if p then
    a
  else
    b) x := by
-- proof
  let ⟨_, h_Iff⟩ := Any_Iff (R := R)
  rw [h_Iff, h_Iff] at *
  apply Cond_Ite.of.AndImpS h


-- created on 2025-04-12
