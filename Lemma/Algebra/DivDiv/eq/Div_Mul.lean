import Lemma.Algebra.Div_Mul.eq.DivDiv
open Algebra


@[main]
private lemma main
  [DivisionCommMonoid α]
  {a b c : α} :
-- imply
  a / b / c = a / (b * c)  := by
-- proof
  rw [Div_Mul.eq.DivDiv]


-- created on 2024-07-01
