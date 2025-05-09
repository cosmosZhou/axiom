import Axiom.Algebra.Abs.eq.IteLt_0
import Axiom.Algebra.EqNegNeg
import Axiom.Algebra.AbsNeg.eq.Abs
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x : α} :
-- imply
  |x| = if x > 0 then
    x
  else
    -x := by
-- proof
  have h := Abs.eq.IteLt_0 (x := -x)
  rw [EqNegNeg] at h
  rw [AbsNeg.eq.Abs] at h
  simp at h
  assumption


-- created on 2025-04-18
