import Lemma.Logic.Ite.eq.IteNot
import Lemma.Algebra.Min.eq.IteGe
open Logic Algebra


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b = if a < b then
    a
  else
    b := by
-- proof
  rw [Ite.eq.IteNot]
  rw [Min.eq.IteGe]
  simp


-- created on 2025-05-07
