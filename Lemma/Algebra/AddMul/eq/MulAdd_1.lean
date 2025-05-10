import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra


@[main]
private lemma main
  [Semiring α]
  {k d : α} :
-- imply
  k * d + d = (k + 1) * d := by
-- proof
  rw [MulAdd.eq.AddMulS]
  simp


-- created on 2025-03-30
