import Lemma.Algebra.Ne.of.Lt
import Lemma.Algebra.Abs.eq.Neg.of.Lt_0
open Algebra


@[main]
private lemma main
  {d: ℤ}
-- given
  (h : d < 0)
  (n : ℤ) :
-- imply
  n % d < -d := by
-- proof
  have := Ne.of.Lt h
  have := Int.emod_lt_abs (a := n) this
  rw [Abs.eq.Neg.of.Lt_0 h] at this
  assumption


-- created on 2025-03-20
-- updated on 2025-03-29
