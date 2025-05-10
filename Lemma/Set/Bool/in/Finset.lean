import Lemma.Logic.Bool.eq.Ite
import Lemma.Set.MemIte.of.OrAndS
import Lemma.Logic.Or_Not.law_of_excluded_middle
open Logic Set


@[main]
private lemma main
  [Decidable p] :
-- imply
  (Bool.toNat p) ∈ ({0, 1} : Set ℕ) := by
-- proof
  rw [Bool.eq.Ite (p := p)]
  apply MemIte.of.OrAndS
  simp
  apply Or_Not.law_of_excluded_middle


-- created on 2025-04-20
