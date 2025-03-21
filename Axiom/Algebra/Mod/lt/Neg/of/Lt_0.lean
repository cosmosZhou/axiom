import Axiom.Algebra.Ne.of.Lt
import Axiom.Algebra.Abs.eq.Neg.of.Lt_0
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n % d < -d := by
-- proof
  have := Ne.of.Lt h
  have := Int.emod_lt (a := n) this
  rw [Abs.eq.Neg.of.Lt_0 h] at this
  assumption


-- created on 2025-03-20
