import Axiom.Algebra.DivMul.eq.Mul_Div
open Algebra


@[main]
private lemma main
  [DivInvMonoid α]
  {a b c : α} :
-- imply
  a * (b / c) = a * b / c := by
-- proof
  rw [DivMul.eq.Mul_Div]


-- created on 2024-07-01
