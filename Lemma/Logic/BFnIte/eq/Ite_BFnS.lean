import Lemma.Logic.Cond_Ite.of.OrAndS
open Logic


@[main]
private lemma main
  [Decidable p]
  {f : β → α → γ}
  {c : α}
  {a b : β} :
-- imply
  f (if p then
    a
  else
    b) c = if p then
    f a c
  else
    f b c := by
-- proof
  apply Cond_Ite.of.OrAndS (R := Eq)
  -- This decomposes the proof into two cases: when `p` is true and when `p` is false.
  split_ifs <;>
    simp_all


-- created on 2025-04-18
