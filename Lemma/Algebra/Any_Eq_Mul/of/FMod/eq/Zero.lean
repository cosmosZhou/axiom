import Lemma.Algebra.FMod.eq.Sub_MulFDiv
import Lemma.Algebra.Eq.of.Sub.eq.Zero
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n.fmod d = 0) :
-- imply
  ∃ k : ℤ, n = k * d := by
-- proof
  rw [FMod.eq.Sub_MulFDiv] at h
  have := Eq.of.Sub.eq.Zero h
  use n // d


-- created on 2025-03-30
