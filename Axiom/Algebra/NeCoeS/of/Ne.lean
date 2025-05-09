import Axiom.Algebra.Sub.ne.Zero.of.Ne
import Axiom.Algebra.CoeSub.eq.SubCoeS
import Axiom.Algebra.Ne.of.Sub.ne.Zero
open Algebra


@[main]
private lemma main
  [AddGroupWithOne R]
  [CharZero R]
  {a b : ℤ}
-- given
  (h : a ≠ b) :
-- imply
  (a : R) ≠ (b : R) := by
-- proof
  have h := Sub.ne.Zero.of.Ne h
  have h : ((a - b : ℤ) : R) ≠ 0 := by 
    apply Int.cast_ne_zero.mpr h
  rw [CoeSub.eq.SubCoeS.int] at h
  apply Ne.of.Sub.ne.Zero h


-- created on 2025-03-30
-- updated on 2025-05-04
