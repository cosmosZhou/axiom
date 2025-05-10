import Lemma.Algebra.Abs.eq.IteGe_0
import Lemma.Logic.OrAndS.of.Cond_Ite
open Algebra Logic


@[main]
private lemma main
  [LinearOrderedRing α]
  {x : α}
-- given
  (h : abs x = 0) :
-- imply
  x = 0 := by
-- proof
  rw [Abs.eq.IteGe_0] at h
  have := OrAndS.of.Cond_Ite h.symm
  simp at this
  cases' this with h h
  ·
    exact h.left.symm
  ·
    exact h.left


-- created on 2025-04-12
