import Axiom.Algebra.SubMulS.eq.MulSub
open Algebra


@[main]
private lemma main
  [Ring α]
  {x a b : α} :
-- imply
  (a - b) * x = a * x - b * x := by
-- proof
  rw [SubMulS.eq.MulSub]


-- created on 2024-11-26
