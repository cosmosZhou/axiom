import Lemma.Algebra.Min.comm
import Lemma.Algebra.Min.eq.IteLe
open Algebra


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b = if a ≥ b then
    b
  else
    a := by
-- proof
  rw [Min.comm]
  rw [Min.eq.IteLe]


-- created on 2025-05-07
