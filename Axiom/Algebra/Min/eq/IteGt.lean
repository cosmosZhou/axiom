import Axiom.Algebra.Min.eq.IteLe
import Axiom.Logic.Ite.eq.IteNot
open Algebra Logic


@[main]
private lemma main
  [LinearOrder α]
-- given
  (a b : α) :
-- imply
  a ⊓ b = if a > b then
    b
  else
    a := by
-- proof
  rw [Ite.eq.IteNot]
  rw [Min.eq.IteLe]
  simp


-- created on 2025-05-07
