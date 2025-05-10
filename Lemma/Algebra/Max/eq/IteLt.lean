import Lemma.Logic.Ite.eq.IteNot
import Lemma.Algebra.Max.eq.IteGe
open Logic Algebra


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊔ b = if a < b then
    b
  else
    a := by
-- proof
  rw [Ite.eq.IteNot]
  rw [Max.eq.IteGe]
  simp


-- created on 2025-05-07
