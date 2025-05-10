import Lemma.Algebra.OrEqS_0.of.Mul.eq.Zero
import Lemma.Algebra.Square.eq.Mul
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
  {x : α}
-- given
  (h : x² = 0) :
-- imply
  x = 0 := by
-- proof
  rw [Square.eq.Mul] at h
  have h := OrEqS_0.of.Mul.eq.Zero h
  cases h <;> assumption


-- created on 2025-01-26
-- updated on 2025-04-06
