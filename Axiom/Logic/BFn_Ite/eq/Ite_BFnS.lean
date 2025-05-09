import Axiom.Logic.Cond_Ite.of.OrAndS
open Logic


@[main]
private lemma main
  [Decidable p]
  {f : α → β → γ}
  {c : α}
  {a b : β} :
-- imply
  f c (if p then
    a
  else
    b) = if p then
    f c a
  else
    f c b := by
-- proof
  apply Cond_Ite.of.OrAndS (R := Eq)
  -- This decomposes the proof into two cases: when `p` is true and when `p` is false.
  split_ifs <;>
    simp_all


-- created on 2025-04-12
