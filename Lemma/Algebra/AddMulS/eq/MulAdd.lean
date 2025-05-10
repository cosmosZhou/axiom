import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra


@[main]
private lemma main
  [Mul α] [Add α] [RightDistribClass α]
  {a b c : α} :
-- imply
  a * c + b * c = (a + b) * c := by
-- proof
  rw [MulAdd.eq.AddMulS]


-- created on 2024-07-01
