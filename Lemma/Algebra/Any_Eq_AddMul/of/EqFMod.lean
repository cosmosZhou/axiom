import Lemma.Algebra.FMod.eq.Sub_MulFDiv
import Lemma.Algebra.Eq_Add.of.EqSub
import Lemma.Algebra.Add.comm
open Algebra


@[main]
private lemma main
  {n d r : ℤ}
-- given
  (h : n.fmod d = r) :
-- imply
  ∃ q : ℤ, n = q * d + r := by
-- proof
  rw [FMod.eq.Sub_MulFDiv] at h
  have := Eq_Add.of.EqSub h
  rw [Add.comm] at this
  use n // d


-- created on 2025-03-30
