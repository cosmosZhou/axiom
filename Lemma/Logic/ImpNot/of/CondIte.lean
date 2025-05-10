import Lemma.Logic.Any_Iff
import Lemma.Logic.ImpNot.of.Cond_Ite
open Logic


@[main]
private lemma main
  [Decidable p]
  {R : β → α → Prop}
  {x : α}
  {a b : β}
  (h : R (if p then
    a
  else
    b) x) :
-- imply
  ¬p → R b x := by
-- proof
  let ⟨_, h_Iff⟩ := Any_Iff (R := R)
  rw [h_Iff] at *
  apply ImpNot.of.Cond_Ite h


-- created on 2025-04-12
