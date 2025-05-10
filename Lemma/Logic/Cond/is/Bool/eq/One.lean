import Lemma.Logic.Bool.eq.Ite
open Logic


@[main]
private lemma main
  [Decidable p] :
-- imply
  p ↔ Bool.toNat p = 1 := by
-- proof
  rw [Bool.eq.Ite]
  simp


-- created on 2025-04-20
