import Lemma.Algebra.AddMulS.eq.Mul_Add
open Algebra


@[main]
private lemma main
  [Mul α] [Add α] [LeftDistribClass α]
  {x a b : α} :
-- imply
  x * (a + b) = x * a + x * b := by
-- proof
  rw [AddMulS.eq.Mul_Add]


-- created on 2024-07-01
