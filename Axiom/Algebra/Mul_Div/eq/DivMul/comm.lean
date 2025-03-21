import Axiom.Algebra.Mul_Div.eq.DivMul
import Axiom.Algebra.Mul.comm
open Algebra


@[main]
private lemma main
  [Semifield α]
  {a b c : α} :
-- imply
  a * (b / c) = b * a / c := by
-- proof
  rw [Mul_Div.eq.DivMul]
  rw [Mul.comm]


-- created on 2024-07-01
