import Lemma.Algebra.DivMul.eq.MulDiv
open Algebra


@[main]
private lemma main
  [DivisionCommMonoid α]
  {a b c : α} :
-- imply
  a / c * b = a * b / c := by
-- proof
  rw [DivMul.eq.MulDiv]


-- created on 2024-07-01
