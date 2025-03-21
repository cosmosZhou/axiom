import Axiom.Algebra.SubMulS.eq.Mul_Sub
open Algebra


@[main]
private lemma main
  [Ring α]
  {x a b : α} :
-- imply
  x * (a - b) = x * a - x * b := by
-- proof
  rw [SubMulS.eq.Mul_Sub]


-- created on 2024-07-01
