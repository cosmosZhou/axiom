import Lemma.Set.InterInter.eq.Inter_Inter
open Set


@[main]
private lemma main
  {a b c : Set α} :
-- imply
  a ∩ (b ∩ c) = a ∩ b ∩ c :=
-- proof
  InterInter.eq.Inter_Inter.symm


-- created on 2025-05-01
