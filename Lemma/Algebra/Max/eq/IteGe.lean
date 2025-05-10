import Lemma.Algebra.Max.comm
import Lemma.Algebra.Max.eq.IteLe
open Algebra


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊔ b = if a ≥ b then
    a
  else
    b := by
-- proof
  rw [Max.comm]
  rw [Max.eq.IteLe]


-- created on 2025-05-07
